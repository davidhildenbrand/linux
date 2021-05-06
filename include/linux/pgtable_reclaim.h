// SPDX-License-Identifier: GPL-2.0-or-later
/*
 * Page table reclaim.
 *
 * Copyright Red Hat, Inc. 2021
 *
 * Author(s): David Hildenbrand <david@redhat.com>
 */

#include <linux/mm.h>

#ifdef CONFIG_PAGE_TABLE_RECLAIM

void mm_reclaim_pgtables(struct mm_struct *mm);
void task_reclaim_pgtables(struct task_struct *p);
void memcg_reclaim_pgtables(struct mem_cgroup *memcg);
void reclaim_pgtables(void);

#else /* CONFIG_PAGE_TABLE_RECLAIM */

static inline void mm_reclaim_pgtables(struct mm_struct *mm) { }
static inline void task_reclaim_pgtables(struct task_struct *p) { }
static inline void memcg_reclaim_pgtables(struct mem_cgroup *memcg) {}
static inline void reclaim_pgtables(void) { }

#endif /* CONFIG_PAGE_TABLE_RECLAIM */
