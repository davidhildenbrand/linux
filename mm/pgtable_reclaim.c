// SPDX-License-Identifier: GPL-2.0-or-later
/*
 * Page table reclaim.
 *
 * Copyright Red Hat, Inc. 2021
 *
 * Author(s): David Hildenbrand <david@redhat.com>
 */

#include <linux/pgtable_reclaim.h>
#include <linux/sched/mm.h>
#include <linux/hugetlb.h>
#include <linux/pagewalk.h>
#include <asm/pgalloc.h>
#include <asm/tlb.h>
#include <asm/tlbflush.h>
#include "internal.h"

/*
 * Lookup a PMD entry pointer while holding the mmap_lock in write and without
 * any details about the VMA.
 */
pmd_t *lookup_pmdp(struct mm_struct *mm, unsigned long address)
{
	pgd_t *pgdp;
	p4d_t *p4dp;
	pud_t *pudp;

	pgdp = pgd_offset(mm, address);
	if (unlikely(!pgd_present(*pgdp)))
		return NULL;
	if (unlikely(pgd_huge(*pgdp) || is_hugepd(__hugepd(pgd_val(*pgdp)))))
		return NULL;

	p4dp = p4d_offset(pgdp, address);
	if (unlikely(!p4d_present(*p4dp)))
		return NULL;
	if (unlikely(p4d_huge(*p4dp) || is_hugepd(__hugepd(p4d_val(*p4dp)))))
		return NULL;

	pudp = pud_offset(p4dp, address);
	if (unlikely(!pud_present(*pudp)))
		return NULL;
	if (unlikely(pud_huge(*pudp) || is_hugepd(__hugepd(pud_val(*pudp)))))
		return NULL;

	return pmd_offset(pudp, address);
}

/*
 * Lookup a PUD entry pointer while holding the mmap_lock in write and without
 * any details about the VMA.
 */
pud_t *lookup_pudp(struct mm_struct *mm, unsigned long address)
{
	pgd_t *pgdp;
	p4d_t *p4dp;

	pgdp = pgd_offset(mm, address);
	if (unlikely(!pgd_present(*pgdp)))
		return NULL;
	if (unlikely(pgd_huge(*pgdp) || is_hugepd(__hugepd(pgd_val(*pgdp)))))
		return NULL;

	p4dp = p4d_offset(pgdp, address);
	if (unlikely(!p4d_present(*p4dp)))
		return NULL;
	if (unlikely(p4d_huge(*p4dp) || is_hugepd(__hugepd(p4d_val(*p4dp)))))
		return NULL;

	return pud_offset(p4dp, address);
}

static bool pte_table_empty_lockless(pmd_t pmd, unsigned long addr)
{
	const unsigned long end = addr + PMD_SIZE;
	pte_t *ptep, *ptem;

	ptem = ptep = pte_offset_map(&pmd, addr);
	do {
		pte_t pte = ptep_get_lockless(ptep);

		if (!pte_none(pte)) {
			pte_unmap(ptem);
			return false;
		}
	} while (ptep++, addr += PAGE_SIZE, addr != end);

	pte_unmap(ptem);
	return true;
}

static bool pte_table_empty(struct mm_struct *mm, pmd_t *pmdp,
			    unsigned long addr)
{
	const unsigned long end = addr + PMD_SIZE;
	spinlock_t *ptl;
	pte_t *ptep;

	ptep = pte_offset_map_lock(mm, pmdp, addr, &ptl);
	do {
		if (!pte_none(*ptep)) {
			pte_unmap_unlock(ptep, ptl);
			return false;
		}
	} while (ptep++, addr += PAGE_SIZE, addr != end);

	pte_unmap_unlock(ptep, ptl);
	return true;
}

static bool pmd_table_empty_lockless(pud_t *pudp, pud_t pud, unsigned long addr)
{
	const unsigned long end = addr + PUD_SIZE;
	pmd_t *pmdp;

	pmdp = pmd_offset_lockless(pudp, pud, addr);
	do {
		pmd_t pmd = READ_ONCE(*pmdp);

		if (!pmd_none(pmd))
			return false;
	} while (pmdp++, addr += PMD_SIZE, addr != end);

	return true;
}

static bool pmd_table_empty(pud_t *pudp, unsigned long addr)
{
	const unsigned long end = addr + PUD_SIZE;
	pmd_t *pmdp;

	pmdp = pmd_offset(pudp, addr);
	do {
		if (!pmd_none(*pmdp))
			return false;
	} while (pudp++, addr += PMD_SIZE, addr != end);

	return true;
}

static void try_reclaim_pte_table(struct mmu_gather *tlb, pmd_t *pmdp,
				  pmd_t pmd, unsigned long addr)
{
	struct mm_struct *mm = tlb->mm;
	spinlock_t *pmd_ptl;
	pgtable_t table;

	mmap_write_lock(mm);

	/* Re-validate under lock that nothing changed. */
	if (lookup_pmdp(mm, addr) == pmdp &&
	    pmd_val(*pmdp) == pmd_val(pmd) &&
	    pte_table_empty(mm, pmdp, addr)) {
		//printk("Reclaiming PTE table at: %lx\n", addr);

		pmd_ptl = pmd_lock(mm, pmdp);

		/* TODO: use free_pte_range */
		table = pmd_pgtable(*pmdp);
		pmd_clear(pmdp);
		pte_free_tlb(tlb, table, addr);
		mm_dec_nr_ptes(mm);

		spin_unlock(pmd_ptl);
	}

	mmap_write_unlock(mm);
}

static void try_reclaim_pmd_table(struct mmu_gather *tlb, pud_t *pudp,
				  pud_t pud, unsigned long addr)
{
	struct mm_struct *mm = tlb->mm;
	pmd_t *pmd;

	mmap_write_lock(mm);

	/* Re-validate under lock that nothing changed. */
	if (lookup_pudp(mm, addr) == pudp &&
	    pud_val(*pudp) == pud_val(pud) &&
	    pmd_table_empty(pudp, addr)) {
		//printk("Reclaiming PMD table at: %lx\n", addr);

		/* TODO: use free_pmd_range */
		pmd = pmd_offset(pudp, addr);
		pud_clear(pudp);
		pmd_free_tlb(tlb, pmd, addr);
		mm_dec_nr_pmds(mm);
	}

	mmap_write_unlock(mm);
}

static unsigned long reclaim_pgtable_pmd_range(struct mmu_gather *tlb,
					       pud_t *pudp, pud_t pud,
					       unsigned long addr,
					       unsigned long end,
					       bool *irq_enabled)
{
	unsigned long next;
	pmd_t *pmdp;

	pmdp = pmd_offset_lockless(pudp, pud, addr);
	do {
		pmd_t pmd = READ_ONCE(*pmdp);

		next = pmd_addr_end(addr, end);
		if (!pmd_present(pmd))
			continue;
		if (unlikely(pmd_trans_huge(pmd) || pmd_huge(pmd) ||
			    pmd_devmap(pmd) ||
			    is_hugepd(__hugepd(pmd_val(pmd)))))
			continue;

		if (unlikely(!IS_ALIGNED(addr, PMD_SIZE) ||
			     !IS_ALIGNED(next, PMD_SIZE)))
			continue;
		if (pte_table_empty_lockless(pmd, addr)) {
			local_irq_enable();
			*irq_enabled = true;

			try_reclaim_pte_table(tlb, pmdp, pmd, addr);
		}
		return next;
	} while (pmdp++, addr = next, addr != end);

	return end;
}

static unsigned long reclaim_pgtable_pud_range(struct mmu_gather *tlb,
					       p4d_t *p4dp, p4d_t p4d,
					       unsigned long addr,
					       unsigned long end,
					       int level, bool *irq_enabled)
{
	unsigned long next;
	pud_t *pudp;

	pudp = pud_offset_lockless(p4dp, p4d, addr);
	do {
		pud_t pud = READ_ONCE(*pudp);

		next = pud_addr_end(addr, end);
		if (!pud_present(pud))
			continue;
		if (unlikely(pud_huge(pud) ||
			     is_hugepd(__hugepd(pud_val(pud)))))
			continue;
		if (level == 1) {
			if (unlikely(!IS_ALIGNED(addr, PUD_SIZE) ||
				     !IS_ALIGNED(next, PUD_SIZE)))
				continue;
			if (pmd_table_empty_lockless(pudp, pud, addr)) {
				local_irq_enable();
				*irq_enabled = true;

				try_reclaim_pmd_table(tlb, pudp, pud, addr);
			}
			return next;
		}
		return reclaim_pgtable_pmd_range(tlb, pudp, pud, addr, next,
						 irq_enabled);
	} while (pudp++, addr = next, addr != end);

	return end;
}

static unsigned long reclaim_pgtable_p4d_range(struct mmu_gather *tlb,
					       pgd_t *pgdp, pgd_t pgd,
					       unsigned long addr,
					       unsigned long end,
					       int level, bool *irq_enabled)
{
	unsigned long next;
	p4d_t *p4dp;

	p4dp = p4d_offset_lockless(pgdp, pgd, addr);
	do {
		p4d_t p4d = READ_ONCE(*p4dp);

		next = p4d_addr_end(addr, end);
		if (!p4d_present(p4d))
			continue;
		if (unlikely(p4d_huge(p4d) ||
			     is_hugepd(__hugepd(p4d_val(p4d)))))
			continue;
		return reclaim_pgtable_pud_range(tlb, p4dp, p4d, addr, next,
						 level, irq_enabled);
	} while (p4dp++, addr = next, addr != end);

	return end;
}

static unsigned long reclaim_pgtable_pgd_range(struct mmu_gather *tlb,
					       unsigned long addr,
					       unsigned long end, int level,
					       bool *irq_enabled)
{
	unsigned long next;
	pgd_t *pgdp;

	pgdp = pgd_offset(tlb->mm, addr);
	do {
		pgd_t pgd = READ_ONCE(*pgdp);

		next = pgd_addr_end(addr, end);
		if (!pgd_present(pgd))
			continue;
		if (unlikely(pgd_huge(pgd) ||
			     is_hugepd(__hugepd(pgd_val(pgd)))))
			continue;
		return reclaim_pgtable_p4d_range(tlb, pgdp, pgd, addr, next,
						 level, irq_enabled);
	} while (pgdp++, addr = next, addr != end);

	return end;
}

/*
 * Reclaim page tables from a MM context at a certain level.
 *
 * Note: must not be called with the mm_lock held.
 */
static void __mm_reclaim_pgtables(struct mm_struct *mm)
{
	unsigned long next, ceil, addr;
	struct mmu_gather tlb;
	bool irq_enabled;
	int level;

	mmap_read_lock(mm);
	/*
	 * We just need any ceiling to not try walking too much. Especially,
	 * when we don't have 5 levels of page tables and would use 0, we would
	 * scan the same page tables over and over again.
	 */
	ceil = mm->highest_vm_end;
	mmap_read_unlock(mm);

	tlb_gather_mmu(&tlb, mm);

	/*
	 * We scan scan completely lockless with interrupts disabled, similar to
	 * fast GUP. We have to limit the number of page table entries we're
	 * scanning at a time, to not have interrupts disabled for too long.
	 *
	 * With interrupts disabled, page tables can get modified and might be
	 * queued up for freeing, however, they won't get freed before
	 * interrupts are re-enabled.
	 *
	 * Once we found a candidate page table, we have to temporarily grab
	 * the mm lock in write and re-verify our result, freeing the page
	 * table.
	 *
	 * For now, we only try removing the lowest two hierarchies.
	 *
	 * Note: scanning with mma_lock in read is not safe, we would have to
	 * hold it in write.
	 *
	 * TODO: Right now, in the worst case we scan one complete page table
	 * (e.g., 512 entries) with interrupts disabled. KVM code scans at most
	 * 8, however, performs actual GUP. If 512 turns out to be too much,
	 * we'd have to chunk it, and remember the previously state for a
	 * page table.
	 */
	for (level = 0; level < 2; level++) {
		addr = FIRST_USER_ADDRESS;
		do {
			irq_enabled = false;

			local_irq_disable();
			next = reclaim_pgtable_pgd_range(&tlb, addr, ceil,
							 level, &irq_enabled);
			if (!irq_enabled)
				local_irq_enable();

			if (unlikely(fatal_signal_pending(current)))
				break;

			cond_resched();
		} while (addr = next, addr != ceil);
	}
	tlb_finish_mmu(&tlb);
}

/*
 * Zap page table entries that might help reclaiming page tables from a MM
 * context and reclaim page tables.
 *
 * Note: must not be called with the mm_lock held.
 */
void mm_reclaim_pgtables(struct mm_struct *mm)
{
	struct mmu_gather tlb;
	printk("Reclaiming: %p\n", mm);

	/*
	 * Scan and remove completely empty page tables.
	 */
	__mm_reclaim_pgtables(mm);
}

/*
 * Reclaim page tables from a process. Called under get_task_struct().
 *
 * Note: must not be called with the mm_lock held.
 */
void task_reclaim_pgtables(struct task_struct *p)
{
	if (unlikely(!p || !p->mm))
		return;

	/*
	 * TODO: We'd like to avoid a mmget and instad use mmgrab ...
	 * but it's difficult racing with exit_mmap(). We could only
	 * mmgrab here and do an mmget_not_zero() everytime we do another
	 * iteration of page table freeing (where we drop all locks either way)/
	 */
	if (!mmget_not_zero(p->mm)) {
		return;
	}
	mm_reclaim_pgtables(p->mm);
	mmput(p->mm);
}

static int __memcg_reclaim_pgtables(struct task_struct *p, void *opaque)
{
	task_reclaim_pgtables(p);
	if (unlikely(fatal_signal_pending(current)))
		return -EINTR;
	return 0;
}

void memcg_reclaim_pgtables(struct mem_cgroup *memcg)
{
	if (!memcg || memcg == root_mem_cgroup)
		reclaim_pgtables();
	else
		mem_cgroup_scan_tasks(memcg, __memcg_reclaim_pgtables, NULL);
}

/*
 * Try to reclaim page tables from all present processes.
 *
 * Note: must not be called with any mm_lock held.
 */
void reclaim_pgtables(void)
{
	struct task_struct *p, *next_p;

	p = &init_task;
	get_task_struct(p);
	task_reclaim_pgtables(p);

	while (true) {
		rcu_read_lock();
		next_p = next_task(p);
		put_task_struct(p);
		p = next_p;
		get_task_struct(p);
		rcu_read_unlock();

		if (p == &init_task)
			break;

		task_reclaim_pgtables(p);

		if (unlikely(fatal_signal_pending(current)))
			break;
		cond_resched();
	}

	put_task_struct(p);
}

#ifdef CONFIG_SYSFS

static ssize_t zap_zero_pages_show(struct kobject *kobj,
				      struct kobj_attribute *attr, char *buf)
{
	return sysfs_emit(buf, "%d\n", zap_zero_pages);
}

static ssize_t zap_zero_pages_store(struct kobject *kobj,
				       struct kobj_attribute *attr,
				       const char *buf, size_t count)
{
	unsigned long value;
	int ret;

	ret = kstrtoul(buf, 10, &value);
	if (ret < 0)
		return ret;
	if (value > 1)
		return -EINVAL;

	zap_zero_pages = value;
	return count;
}

static struct kobj_attribute zap_zero_pages_attr =
	__ATTR_RW(zap_zero_pages);

static struct attribute *pgtable_reclaim_attrs[] = {
	&zap_zero_pages_attr.attr,
	NULL,
};

static const struct attribute_group pgtable_reclaim_attr_group = {
	.attrs = pgtable_reclaim_attrs,
};

static int pgtable_reclaim_init_sysfs(struct kobject **sysfs_kobj)
{
	int ret;

	*sysfs_kobj = kobject_create_and_add("pgtable_reclaim", mm_kobj);
	if (unlikely(!*sysfs_kobj)) {
		pr_err("failed to create sysfs pgtable_reclaim kobject\n");
		return -ENOMEM;
	}

	ret = sysfs_create_group(*sysfs_kobj, &pgtable_reclaim_attr_group);
	if (ret) {
		pr_err("failed to register pgtable_reclaim group\n");
		kobject_put(*sysfs_kobj);
		return ret;
	}

	return 0;
}

//static void pgtable_reclaim_deinit_sysfs(struct kobject *sysfs_kobj)
//{
//	sysfs_remove_group(sysfs_kobj, &pgtable_reclaim_attr_group);
//	kobject_put(sysfs_kobj);
//}
#else
static inline int pgtable_reclaim_init_sysfs(struct kobject **sysfs_kobj)
{
	return 0;
}

//static inline void pgtable_reclaim_deinit_sysfs(struct kobject *sysfs_kobj)
//{
//}
#endif /* CONFIG_SYSFS */

static int __init pgtable_reclaim_init(void)
{
	struct kobject *sysfs_kobj;
	int ret;

	ret = pgtable_reclaim_init_sysfs(&sysfs_kobj);
	if (ret)
		return ret;

	return 0;
}

subsys_initcall(pgtable_reclaim_init);
