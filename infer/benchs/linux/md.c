/*
   md.c : Multiple Devices driver for Linux
      Copyright (C) 1998, 1999, 2000 Ingo Molnar

     completely rewritten, based on the MD driver code from Marc Zyngier

   Changes:

   - RAID-1/RAID-5 extensions by Miguel de Icaza, Gadi Oxman, Ingo Molnar
   - RAID-6 extensions by H. Peter Anvin <hpa@zytor.com>
   - boot support for linear and striped mode by Harald Hoyer <HarryH@Royal.Net>
   - kerneld support by Boris Tobotras <boris@xtalk.msk.su>
   - kmod support by: Cyrus Durgin
   - RAID0 bugfixes: Mark Anthony Lisher <markal@iname.com>
   - Devfs support by Richard Gooch <rgooch@atnf.csiro.au>

   - lots of fixes and improvements to the RAID1/RAID5 and generic
     RAID code (such as request based resynchronization):

     Neil Brown <neilb@cse.unsw.edu.au>.

   - persistent bitmap code
     Copyright (C) 2003-2004, Paul Clements, SteelEye Technology, Inc.

   This program is free software; you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation; either version 2, or (at your option)
   any later version.

   You should have received a copy of the GNU General Public License
   (for example /usr/src/linux/COPYING); if not, write to the Free
   Software Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.
*/

#define NULL ((void *)0)

typedef unsigned long long __u64;
typedef unsigned long long sector_t;

/*
 * Simple doubly linked list implementation.
 *
 * Some of the internal functions ("__xxx") are useful when
 * manipulating whole lists rather than single entries, as
 * sometimes we already know the next/prev entries and we can
 * generate better code by using them directly rather than
 * using the generic single-entry routines.
 */
struct list_head {
    struct list_head *next, *prev;
};

#define LIST_HEAD_INIT(name) { &(name), &(name) }

#define LIST_HEAD(name) \
    struct list_head name = LIST_HEAD_INIT(name)

static inline void INIT_LIST_HEAD(struct list_head *list)
{
    list->next = list;
    list->prev = list;
}

/*
 * Insert a new entry between two known consecutive entries.
 *
 * This is only for internal list manipulation where we know
 * the prev/next entries already!
 */
static inline __attribute__((always_inline)) void __list_add(
        struct list_head *new, struct list_head *prev, struct list_head *next) {
    next->prev = new;
    new->next = next;
    new->prev = prev;
    prev->next = new;
}

/**
 * list_add - add a new entry
 * @new: new entry to be added
 * @head: list head to add it after
 *
 * Insert a new entry after the specified head.
 * This is good for implementing stacks.
 */
static inline void list_add(struct list_head *new, struct list_head *head)
{
    __list_add(new, head, head->next);
}

/**
 * list_add_tail - add a new entry
 * @new: new entry to be added
 * @head: list head to add it before
 *
 * Insert a new entry before the specified head.
 * This is useful for implementing queues.
 */
static inline __attribute__((always_inline)) void list_add_tail(
        struct list_head *new, struct list_head *head) {
    __list_add(new, head->prev, head);
}

/*
 * Delete a list entry by making the prev/next entries
 * point to each other.
 *
 * This is only for internal list manipulation where we know
 * the prev/next entries already!
 */
static inline void __list_del(struct list_head * prev, struct list_head * next)
{
    next->prev = prev;
    prev->next = next;
}

/**
 * list_del - deletes entry from list.
 * @entry: the element to delete from the list.
 * Note: list_empty() on entry does not return true after this, the entry is
 * in an undefined state.
 */
static inline void list_del(struct list_head *entry)
{
    __list_del(entry->prev, entry->next);
    /*
     * These are non-NULL pointers that will result in page faults
     * under normal circumstances, used to verify that nobody uses
     * non-initialized list entries.
     */
    entry->next = ((void *) 0x00100100 + (0x0UL));
    entry->prev = ((void *) 0x00200200 + (0x0UL));
}

/**
 * list_del_init - deletes entry from list and reinitialize it.
 * @entry: the element to delete from the list.
 */
static inline void list_del_init(struct list_head *entry)
{
    __list_del(entry->prev, entry->next);
    INIT_LIST_HEAD(entry);
}

/**
 * list_empty - tests whether a list is empty
 * @head: the list to test.
 */
static inline int list_empty(const struct list_head *head)
{
    return head->next == head;
}

/**
 * list_del_rcu - deletes entry from list without re-initialization
 * @entry: the element to delete from the list.
 *
 * Note: list_empty() on entry does not return true after this,
 * the entry is in an undefined state. It is useful for RCU based
 * lockfree traversal.
 *
 * In particular, it means that we can not poison the forward
 * pointers that may still be used for walking the list.
 *
 * The caller must take whatever precautions are necessary
 * (such as holding appropriate locks) to avoid racing
 * with another list-mutation primitive, such as list_del_rcu()
 * or list_add_rcu(), running on this same list.
 * However, it is perfectly legal to run concurrently with
 * the _rcu list-traversal primitives, such as
 * list_for_each_entry_rcu().
 *
 * Note that the caller is not permitted to immediately free
 * the newly deleted entry.  Instead, either synchronize_rcu()
 * or call_rcu() must be used to defer freeing until an RCU
 * grace period has elapsed.
 */
static inline void list_del_rcu(struct list_head *entry)
{
    __list_del(entry->prev, entry->next);
    entry->prev = NULL;
}

/****************************************************************************/
/*
 * Enables to iterate over all existing md arrays
 * all_mddevs_lock protects this list.
 */
static LIST_HEAD(all_mddevs);
static LIST_HEAD(pers_list);

typedef unsigned int dev_t;

typedef struct {
    int counter;
} atomic_t;

struct kref {
    atomic_t refcount;
};

struct hd_struct {
    sector_t start_sect;
    sector_t nr_sects;
    sector_t alignment_offset;
//  unsigned int discard_alignment;
//  struct device __dev;
//  struct kobject *holder_dir;
//  int policy, partno;
//
//  unsigned long stamp;
//  int in_flight[2];
//
//  struct disk_stats dkstats;
//
//  struct rcu_head rcu_head;
};

struct gendisk {
//  int major;
//  int first_minor;
//  int minors;
//
//  char disk_name[32];
//  char *(*devnode)(struct gendisk *gd, mode_t *mode);
//
//  struct disk_part_tbl *part_tbl;
    struct hd_struct part0;
//
//  const struct block_device_operations *fops;
//  struct request_queue *queue;
//  void *private_data;
//
//  int flags;
//  struct device *driverfs_dev;
//  struct kobject *slave_dir;
//
//  struct timer_rand_state *random;
//
//  atomic_t sync_io;
//  struct work_struct async_notify;
//  int node_id;
};

struct kobject {
    const char      *name;
    struct list_head    entry;
//  struct kobject      *parent;
//  struct kset     *kset;
//  struct kobj_type    *ktype;
//  struct sysfs_dirent *sd;
    struct kref     kref;
//  unsigned int state_initialized:1;
//  unsigned int state_in_sysfs:1;
//  unsigned int state_add_uevent_sent:1;
//  unsigned int state_remove_uevent_sent:1;
//  unsigned int uevent_suppress:1;
};

struct mdk_personality
{
    char *name;
    int level;
    struct list_head list;
//  struct module *owner;
//  int (*make_request)(mddev_t *mddev, struct bio *bio);
//  int (*run)(mddev_t *mddev);
//  int (*stop)(mddev_t *mddev);
//  void (*status)(struct seq_file *seq, mddev_t *mddev);
//  /* error_handler must set ->faulty and clear ->in_sync
//   * if appropriate, and should abort recovery if needed
//   */
//  void (*error_handler)(mddev_t *mddev, mdk_rdev_t *rdev);
//  int (*hot_add_disk) (mddev_t *mddev, mdk_rdev_t *rdev);
//  int (*hot_remove_disk) (mddev_t *mddev, int number);
//  int (*spare_active) (mddev_t *mddev);
//  sector_t (*sync_request)(mddev_t *mddev, sector_t sector_nr, int *skipped, int go_faster);
//  int (*resize) (mddev_t *mddev, sector_t sectors);
//  sector_t (*size) (mddev_t *mddev, sector_t sectors, int raid_disks);
//  int (*check_reshape) (mddev_t *mddev);
//  int (*start_reshape) (mddev_t *mddev);
//  void (*finish_reshape) (mddev_t *mddev);
//  /* quiesce moves between quiescence states
//   * 0 - fully active
//   * 1 - no new requests allowed
//   * others - reserved
//   */
//  void (*quiesce) (mddev_t *mddev, int state);
//  /* takeover is used to transition an array from one
//   * personality to another.  The new personality must be able
//   * to handle the data in the current layout.
//   * e.g. 2drive raid1 -> 2drive raid5
//   *      ndrive raid5 -> degraded n+1drive raid6 with special layout
//   * If the takeover succeeds, a new 'private' structure is returned.
//   * This needs to be installed and then ->run used to activate the
//   * array.
//   */
//  void *(*takeover) (mddev_t *mddev);
};

struct mddev_s
{
//  void                *private;
    struct mdk_personality      *pers;
    dev_t               unit;
    int             md_minor;
    struct list_head        disks;
//  unsigned long           flags;
//#define MD_CHANGE_DEVS    0   /* Some device status has changed */
//#define MD_CHANGE_CLEAN 1 /* transition to or from 'clean' */
//#define MD_CHANGE_PENDING 2   /* superblock update in progress */
//
//  int             suspended;
//  atomic_t            active_io;
    int             ro;
//
    struct gendisk          *gendisk;
//
    struct kobject          kobj;
    int             hold_active;
//#define   UNTIL_IOCTL 1
//#define   UNTIL_STOP  2
//
//  /* Superblock information */
    int             major_version;
//                  minor_version,
//                  patch_version;
    int             persistent;
    int                 external;   /* metadata is
                             * managed externally */
//  char                metadata_type[17]; /* externally set*/
//  int             chunk_sectors;
    long                ctime, utime;
//  int             level, layout;
//  char                clevel[16];
    int             raid_disks;
//  int             max_disks;
    sector_t            dev_sectors;    /* used size of
//                           * component devices */
//  sector_t            array_sectors; /* exported array size */
//  int             external_size; /* size managed
//                          * externally */
    __u64               events;
//  /* If the last 'event' was simply a clean->dirty transition, and
//   * we didn't write it to the spares, then it is safe and simple
//   * to just decrement the event count on a dirty->clean transition.
//   * So we record that possibility here.
//   */
//  int             can_decrease_events;
//
//  char                uuid[16];
//
//  /* If the array is being reshaped, we need to record the
//   * new shape and an indication of where we are up to.
//   * This is written to the superblock.
//   * If reshape_position is MaxSector, then no reshape is happening (yet).
//   */
//  sector_t            reshape_position;
    int             delta_disks;
//  int new_level, new_layout;
//  int             new_chunk_sectors;
//
//  struct mdk_thread_s     *thread;    /* management thread */
//  struct mdk_thread_s     *sync_thread;   /* doing resync or reconstruct */
//  sector_t            curr_resync;    /* last block scheduled */
    /* As resync requests can complete out of order, we cannot easily track
     * how much resync has been completed.  So we occasionally pause until
     * everything completes, then set curr_resync_completed to curr_resync.
     * As such it may be well behind the real resync mark, but it is a value
     * we are certain of.
     */
    sector_t            curr_resync_completed;
//  unsigned long           resync_mark;    /* a recent timestamp */
//  sector_t            resync_mark_cnt;/* blocks written at resync_mark */
//  sector_t            curr_mark_cnt; /* blocks scheduled now */
//
//  sector_t            resync_max_sectors; /* may be set by personality */
//
//  sector_t            resync_mismatches; /* count of sectors where
//                              * parity/replica mismatch found
//                              */
//
//  /* allow user-space to request suspension of IO to regions of the array */
//  sector_t            suspend_lo;
//  sector_t            suspend_hi;
//  /* if zero, use the system-wide default */
//  int             sync_speed_min;
//  int             sync_speed_max;
//
//  /* resync even though the same disks are shared among md-devices */
//  int             parallel_resync;
//
//  int             ok_start_degraded;
//  /* recovery/resync flags
//   * NEEDED:   we might need to start a resync/recover
//   * RUNNING:  a thread is running, or about to be started
//   * SYNC:     actually doing a resync, not a recovery
//   * RECOVER:  doing recovery, or need to try it.
//   * INTR:     resync needs to be aborted for some reason
//   * DONE:     thread is done and is waiting to be reaped
//   * REQUEST:  user-space has requested a sync (used with SYNC)
//   * CHECK:    user-space request for check-only, no repair
//   * RESHAPE:  A reshape is happening
//   *
//   * If neither SYNC or RESHAPE are set, then it is a recovery.
//   */
//#define   MD_RECOVERY_RUNNING 0
//#define   MD_RECOVERY_SYNC    1
//#define   MD_RECOVERY_RECOVER 2
//#define   MD_RECOVERY_INTR    3
//#define   MD_RECOVERY_DONE    4
//#define   MD_RECOVERY_NEEDED  5
//#define   MD_RECOVERY_REQUESTED   6
//#define   MD_RECOVERY_CHECK   7
//#define MD_RECOVERY_RESHAPE   8
//#define   MD_RECOVERY_FROZEN  9
//
//  unsigned long           recovery;
    int             recovery_disabled; /* if we detect that recovery
                                * will always fail, set this
                                * so we don't loop trying */

//  int             in_sync;    /* know to not need resync */
//  /* 'open_mutex' avoids races between 'md_open' and 'do_md_stop', so
//   * that we are never stopping an array while it is open.
//   * 'reconfig_mutex' protects all other reconfiguration.
//   * These locks are separate due to conflicting interactions
//   * with bdev->bd_mutex.
//   * Lock ordering is:
//   *  reconfig_mutex -> bd_mutex : e.g. do_md_run -> revalidate_disk
//   *  bd_mutex -> open_mutex:  e.g. __blkdev_get -> md_open
//   */
//  struct mutex            open_mutex;
//  struct mutex            reconfig_mutex;
    atomic_t            active;     /* general refcount */
    atomic_t            openers;    /* number of active opens */

    int             degraded;   /* whether md should consider
                             * adding a spare
                             */
//  int             barriers_work;  /* initialised to true, cleared as soon
//                           * as a barrier request to slave
//                           * fails.  Only supported
//                           */
//  struct bio          *biolist;   /* bios that need to be retried
//                           * because BIO_RW_BARRIER is not supported
//                           */
//
//  atomic_t            recovery_active; /* blocks scheduled, but not written */
//  wait_queue_head_t       recovery_wait;
//  sector_t            recovery_cp;
//  sector_t            resync_min; /* user requested sync
//                           * starts here */
//  sector_t            resync_max; /* resync should pause
//                           * when it gets here */
//
    struct sysfs_dirent     *sysfs_state;   /* handle for 'array_state'
                             * file in sysfs.
                             */
//  struct sysfs_dirent     *sysfs_action;  /* handle for 'sync_action' */
//
//  struct work_struct del_work;    /* used for delayed sysfs removal */
//
//  spinlock_t          write_lock;
//  wait_queue_head_t       sb_wait;    /* for waiting on superblock updates */
//  atomic_t            pending_writes; /* number of active superblock writes */
//
//  unsigned int            safemode;   /* if set, update "clean" superblock
//                           * when no writes pending.
//                           */
//  unsigned int            safemode_delay;
//  struct timer_list       safemode_timer;
//  atomic_t            writes_pending;
//  struct request_queue        *queue; /* for plugging ... */
//
//  struct bitmap                   *bitmap; /* the bitmap for the device */
//  struct {
//      struct file     *file; /* the bitmap file */
//      loff_t          offset; /* offset from superblock of
//                       * start of bitmap. May be
//                       * negative, but not '0'
//                       * For external metadata, offset
//                       * from start of device.
//                       */
//      loff_t          default_offset; /* this is the offset to use when
//                           * hot-adding a bitmap.  It should
//                           * eventually be settable by sysfs.
//                           */
//      struct mutex        mutex;
//      unsigned long       chunksize;
//      unsigned long       daemon_sleep; /* how many seconds between updates? */
//      unsigned long       max_write_behind; /* write-behind mode */
//      int         external;
//  } bitmap_info;
//
//  atomic_t            max_corr_read_errors; /* max read retries */
    struct list_head        all_mddevs;
//
//  struct attribute_group      *to_remove;
//  /* Generic barrier handling.
//   * If there is a pending barrier request, all other
//   * writes are blocked while the devices are flushed.
//   * The last to finish a flush schedules a worker to
//   * submit the barrier request (without the barrier flag),
//   * then submit more flush requests.
//   */
//  struct bio *barrier;
//  atomic_t flush_pending;
//  struct work_struct barrier_work;
};

struct inode {
//  struct hlist_node i_hash;
//  struct list_head i_list;
//  struct list_head i_sb_list;
//  struct list_head i_dentry;
//  unsigned long i_ino;
//  atomic_t i_count;
//  unsigned int i_nlink;
//  uid_t i_uid;
//  gid_t i_gid;
//  dev_t i_rdev;
//  unsigned int i_blkbits;
//  u64 i_version;
    long long i_size;

//  struct timespec i_atime;
//  struct timespec i_mtime;
//  struct timespec i_ctime;
//  blkcnt_t i_blocks;
//  unsigned short i_bytes;
//  umode_t i_mode;
//  spinlock_t i_lock;
//  struct mutex i_mutex;
//  struct rw_semaphore i_alloc_sem;
//  const struct inode_operations *i_op;
//  const struct file_operations *i_fop;
//  struct super_block *i_sb;
//  struct file_lock *i_flock;
//  struct address_space *i_mapping;
//  struct address_space i_data;
//
//  struct list_head i_devices;
//  union {
//      struct pipe_inode_info *i_pipe;
//      struct block_device *i_bdev;
//      struct cdev *i_cdev;
//  };
//
//  __u32 i_generation;
//  //# 779 "include/linux/fs.h"
//  unsigned long i_state;
//  unsigned long dirtied_when;
//
//  unsigned int i_flags;
//
//  atomic_t i_writecount;
//
//  struct posix_acl *i_acl;
//  struct posix_acl *i_default_acl;
//
//  void *i_private;
};
//# 806 "include/linux/fs.h"
enum inode_i_mutex_lock_class {
    I_MUTEX_NORMAL,
    I_MUTEX_PARENT,
    I_MUTEX_CHILD,
    I_MUTEX_XATTR,
    I_MUTEX_QUOTA
};

struct block_device {
    dev_t bd_dev;
    struct inode * bd_inode;
//  struct super_block * bd_super;
//  int bd_openers;
//  struct mutex bd_mutex;
//  struct list_head bd_inodes;
//  void * bd_claiming;
//  void * bd_holder;
//  int bd_holders;
//
//  struct list_head bd_holder_list;
//
//  struct block_device * bd_contains;
//  unsigned bd_block_size;
//  struct hd_struct * bd_part;
//
//  unsigned bd_part_count;
//  int bd_invalidated;
//  struct gendisk * bd_disk;
//  struct list_head bd_list;
//
//  unsigned long bd_private;
//
//  int bd_fsfreeze_count;
//
//  struct mutex bd_fsfreeze_mutex;
};
typedef struct mddev_s mddev_t;

/*
 * Each physical page in the system has a struct page associated with
 * it to keep track of whatever it is we are using the page for at the
 * moment. Note that we have no way to track which tasks are using
 * a page, though if it is a pagecache page, rmap structures can tell us
 * who is mapping it.
 */
struct page {
    unsigned long flags;        /* Atomic flags, some possibly
                     * updated asynchronously */
    atomic_t _count;        /* Usage count, see below. */
//  union {
//      atomic_t _mapcount; /* Count of ptes mapped in mms,
//                   * to show when page is mapped
//                   * & limit reverse map searches.
//                   */
//      struct {        /* SLUB */
//          u16 inuse;
//          u16 objects;
//      };
//  };
//  union {
//      struct {
//      unsigned long private;      /* Mapping-private opaque data:
//                       * usually used for buffer_heads
//                       * if PagePrivate set; used for
//                       * swp_entry_t if PageSwapCache;
//                       * indicates order in the buddy
//                       * system if PG_buddy is set.
//                       */
//      struct address_space *mapping;  /* If low bit clear, points to
//                       * inode address_space, or NULL.
//                       * If page mapped as anonymous
//                       * memory, low bit is set, and
//                       * it points to anon_vma object:
//                       * see PAGE_MAPPING_ANON below.
//                       */
//      };
//#if USE_SPLIT_PTLOCKS
//      spinlock_t ptl;
//#endif
//      struct kmem_cache *slab;    /* SLUB: Pointer to slab */
//      struct page *first_page;    /* Compound tail pages */
//  };
//  union {
//      pgoff_t index;      /* Our offset within mapping. */
//      void *freelist;     /* SLUB: freelist req. slab lock */
//  };
//  struct list_head lru;       /* Pageout list, eg. active_list
//                   * protected by zone->lru_lock !
//                   */
//  /*
//   * On machines where all RAM is mapped into kernel address space,
//   * we can simply calculate the virtual address. On machines with
//   * highmem some memory is mapped into kernel virtual memory
//   * dynamically, so we need a place to store that address.
//   * Note that this field could be 16 bits on x86 ... ;)
//   *
//   * Architectures with slow multiplication can define
//   * WANT_PAGE_VIRTUAL in asm/page.h
//   */
//#if defined(WANT_PAGE_VIRTUAL)
//  void *virtual;          /* Kernel virtual address (NULL if
//                     not kmapped, ie. highmem) */
//#endif /* WANT_PAGE_VIRTUAL */
//#ifdef CONFIG_WANT_PAGE_DEBUG_FLAGS
//  unsigned long debug_flags;  /* Use atomic bitops on this */
//#endif
//
//#ifdef CONFIG_KMEMCHECK
//  /*
//   * kmemcheck wants to track the status of each byte in a page; this
//   * is a pointer to such a status block. NULL if not tracked.
//   */
//  void *shadow;
//#endif
};

struct sysfs_dirent {
    atomic_t        s_count;
    atomic_t        s_active;
//#ifdef CONFIG_DEBUG_LOCK_ALLOC
//  struct lockdep_map  dep_map;
//#endif
//  struct sysfs_dirent *s_parent;
//  struct sysfs_dirent *s_sibling;
//  const char      *s_name;
//
//  const void      *s_ns; /* namespace tag */
//  union {
//      struct sysfs_elem_dir       s_dir;
//      struct sysfs_elem_symlink   s_symlink;
//      struct sysfs_elem_attr      s_attr;
//      struct sysfs_elem_bin_attr  s_bin_attr;
//  };
//
//  unsigned int        s_flags;
//  unsigned short      s_mode;
//  ino_t           s_ino;
//  struct sysfs_inode_attrs *s_iattr;
};

/*
 * MD's 'extended' device
 */
struct mdk_rdev_s
{
    struct list_head same_set;  /* RAID devices within the same set */

    sector_t sectors;       /* Device size (in 512bytes sectors) */
    mddev_t *mddev;         /* RAID array if running */
//  int last_events;        /* IO event timestamp */
//
    struct block_device *bdev;  /* block device handle */

    struct page *sb_page;
    int     sb_loaded;
    __u64       sb_events;
    sector_t    data_offset;    /* start of data in array */
    sector_t    sb_start;   /* offset of the super block (in 512byte sectors) */
//  int     sb_size;    /* bytes in the superblock */
//  int     preferred_minor;    /* autorun support */
//
    struct kobject  kobj;

    /* A device can be in one of three states based on two flags:
     * Not working:   faulty==1 in_sync==0
     * Fully working: faulty==0 in_sync==1
     * Working, but not
     * in sync with array
     *                faulty==0 in_sync==0
     *
     * It can never have faulty==1, in_sync==1
     * This reduces the burden of testing multiple flags in many cases
     */

    unsigned long   flags;
//#define   Faulty      1       /* device is known to have a fault */
//#define   In_sync     2       /* device is in_sync with rest of array */
//#define   WriteMostly 4       /* Avoid reading if at all possible */
//#define   BarriersNotsupp 5       /* BIO_RW_BARRIER is not supported */
//#define   AllReserved 6       /* If whole device is reserved for
//                   * one array */
//#define   AutoDetected    7       /* added by auto-detect */
//#define Blocked       8       /* An error occured on an externally
//                   * managed array, don't allow writes
//                   * until it is cleared */
//  wait_queue_head_t blocked_wait;
//
    int desc_nr;            /* descriptor index in the superblock */
    int raid_disk;          /* role of device in array */
//  int new_raid_disk;      /* role that the device will have in
//                   * the array after a level-change completes.
//                   */
    int saved_raid_disk;        /* role that device used to have in the
//                   * array and could again if we did a partial
//                   * resync from the bitmap
//                   */
    sector_t    recovery_offset;/* If this device has been partially
                     * recovered, this is where we were
                     * up to.
                     */

    atomic_t    nr_pending; /* number of pending requests.
                     * only maintained for arrays that
                     * support hot removal
                     */
    atomic_t    read_errors;    /* number of consecutive read errors that
                     * we have tried to ignore.
                     */
//  struct timespec last_read_error;    /* monotonic time since our
//                       * last read error
//                       */
    atomic_t    corrected_errors; /* number of corrected read errors,
                       * for reporting to userspace and storing
                       * in superblock.
                       */
//  struct work_struct del_work;    /* used for delayed sysfs removal */
//
    struct sysfs_dirent *sysfs_state; /* handle for 'state'
                       * sysfs entry */
};
typedef struct mdk_rdev_s mdk_rdev_t;

struct seq_file {
    char *buf;
    unsigned int size;
    unsigned int from;
    unsigned int count;
    long long index;
    long long read_pos;
    unsigned long long version;
//  const struct seq_operations *op;
    void *private;
};

struct super_type  {
    char            *name;
//  struct module       *owner;
    int         (*load_super)(mdk_rdev_t *rdev, mdk_rdev_t *refdev,
                      int minor_version);
//  int         (*validate_super)(mddev_t *mddev, mdk_rdev_t *rdev);
    void            (*sync_super)(mddev_t *mddev, mdk_rdev_t *rdev);
    unsigned long long  (*rdev_size_change)(mdk_rdev_t *rdev,
                        sector_t num_sectors);
};

static LIST_HEAD(all_detected_devices);
struct detected_devices_node {
    struct list_head list;
    dev_t dev;
};

/****************************************************************************/

void prefetch(void *x)
{
    return;
}

/**
 * strcmp - Compare two strings
 * @cs: One string
 * @ct: Another string
 *
 * returns   0 if @cs and @ct are equal,
 *         < 0 if @cs is less than @ct
 *         > 0 if @cs is greater than @ct
 */
int strcmp(const char *cs, const char *ct)
{
     int a; return a;
}

void bd_release_from_disk(struct block_device * x, struct gendisk * y){
    return;
}

/**
 *  sysfs_remove_link - remove symlink in object's directory.
 *  @kobj:  object we're acting for.
 *  @name:  name of the symlink to remove.
 */
void sysfs_remove_link(struct kobject *kobj, const char *name){
    return;
}

void sysfs_put(struct sysfs_dirent *sd){
    return;
}

/**
 * strict_strtoull - convert a string to an unsigned long long strictly
 * @cp: The string to be converted
 * @base: The number base to use
 * @res: The converted result value
 *
 * strict_strtoull converts a string to an unsigned long long only if the
 * string is really an unsigned long long string, any string containing
 * any invalid char at the tail will be rejected and -EINVAL is returned,
 * only a newline char at the tail is acceptible because people generally
 * change a module parameter in the following way:
 *
 *  echo 1024 > /sys/module/e1000/parameters/copybreak
 *
 * echo will append a newline to the tail of the string.
 *
 * It returns 0 if conversion is successful and *res is set to the converted
 * value, otherwise it returns -EINVAL and *res is set to 0.
 *
 * simple_strtoull just ignores the successive invalid characters and
 * return the converted value of prefix part of the string.
 */
int strict_strtoull(const char * x, unsigned int y, unsigned long long *z){
    return 0;
}

/**
 * kobject_init - initialize a kobject structure
 * @kobj: pointer to the kobject to initialize
 * @ktype: pointer to the ktype for this kobject.
 *
 * This function will properly initialize a kobject such that it can then
 * be passed to the kobject_add() call.
 *
 * After this function is called, the kobject MUST be cleaned up by a call
 * to kobject_put(), not by a call to kfree directly to ensure that all of
 * the memory is cleaned up properly.
 */
//void kobject_init(struct kobject *kobj, struct kobj_type *ktype)
//{
//  return;
//}

static inline __attribute__((always_inline)) void * ERR_PTR(long error) {
    return (void *) error;
}

static int alloc_disk_sb(mdk_rdev_t * rdev)
{
    return 0;
}

/*
 * prevent the device from being mounted, repartitioned or
 * otherwise reused by a RAID array (or any other kernel
 * subsystem), by bd_claiming the device.
 */
static int lock_rdev(mdk_rdev_t *rdev, dev_t dev, int shared)
{
    int err = 0;
    return err;
}

static void unlock_rdev(mdk_rdev_t *rdev)
{
    return;
}

void put_page(struct page *page)
{
    return;
}

static void free_disk_sb(mdk_rdev_t * rdev)
{
    if (rdev->sb_page) {
        put_page(rdev->sb_page);
        rdev->sb_loaded = 0;
        rdev->sb_page = NULL;
        rdev->sb_start = 0;
        rdev->sectors = 0;
    }
}

void set_disk_ro(struct gendisk *disk, int flag)
{
    return;
}

static void md_stop(mddev_t *mddev)
{
    return;
}

void sysfs_notify_dirent(struct sysfs_dirent *sd)
{
    return;
}

static inline __attribute__((always_inline)) void set_capacity(
        struct gendisk *disk, sector_t size) {
    disk->part0.nr_sects = size;
}

/**
 * blk_integrity_unregister - Remove block integrity profile
 * @disk:   disk whose integrity profile to deallocate
 *
 * Description: This function frees all memory used by the block
 * integrity profile.  To be called at device teardown.
 */
void blk_integrity_unregister(struct gendisk *disk)
{
    return;
}

/**
 * revalidate_disk - wrapper for lower-level driver's revalidate_disk call-back
 * @disk: struct gendisk to be revalidated
 *
 * This routine is a wrapper for lower-level driver's revalidate_disk
 * call-backs.  It is used to do common pre and post operations needed
 * for all revalidate_disk operations.
 */
int revalidate_disk(struct gendisk *disk)
{
    int ret = 0;
    return ret;
}

int register_md_personality(struct mdk_personality *p)
{
    list_add_tail(&p->list, &pers_list);
    return 0;
}

int unregister_md_personality(struct mdk_personality *p)
{
    list_del_init(&p->list);
    return 0;
}

/*
 * lets try to run arrays based on all disks that have arrived
 * until now. (those are in pending_raid_disks)
 *
 * the method: pick the first pending disk, collect all disks with
 * the same UUID, remove all from the pending list and put them into
 * the 'same_array' list. Then order this list based on superblock
 * update time (freshest comes first), kick out 'old' disks and
 * compare superblocks. If everything's fine then run it.
 *
 * If "unit" is allocated, then bump its reference count
 */
static void autorun_devices(int part)
{
    return;
}

static inline __attribute__((always_inline)) long IS_ERR(const void *ptr)
{
    return __builtin_expect(!!(((unsigned long)ptr) >= (unsigned long)-4095), 0);
}

static inline void set_bit(int nr, void *addr)
{
    return;
}

/****************************************************************************/
#define atomic_set(v,i)             ((v)->counter = (i))
#define atomic_inc(v)               ((v)->counter += 1)
#define atomic_dec_and_test(v)      ((v)->counter-1 == 0)
#define atomic_read(v)              ((v)->counter)

/**
 * kref_init - initialize object.
 * @kref: object in question.
 */
void kref_init(struct kref *kref)
{
    atomic_set(&kref->refcount, 1);
}

/**
 * kref_get - increment refcount for object.
 * @kref: object.
 */
void kref_get(struct kref *kref)
{
    atomic_inc(&kref->refcount);
}

/**
 * kobject_get - increment refcount for object.
 * @kobj: object.
 */
struct kobject *kobject_get(struct kobject *kobj)
{
    if (kobj)
        kref_get(&kobj->kref);
    return kobj;
}

static int overlaps(sector_t s1, sector_t l1, sector_t s2, sector_t l2)
{
    /* check if two start/length pairs overlap */
    if (s1+l1 <= s2)
        return 0;
    if (s2+l2 <= s1)
        return 0;
    return 1;
}

/****************************************************************************/
static atomic_t md_event_count;
void md_new_event(mddev_t *mddev)
{
    atomic_inc(&md_event_count);
    return;
}

static void mddev_put(mddev_t *mddev)
{
    if (!mddev->raid_disks && list_empty(&mddev->disks) &&
        mddev->ctime == 0 && !mddev->hold_active) {
        /* Array is not configured at all, and not held active,
         * so destroy it */
        list_del(&mddev->all_mddevs);
        if (mddev->gendisk) {
            /* we did a probe so need to clean up.
             * Call schedule_work inside the spinlock
             * so that flush_scheduled_work() after
             * mddev_find will succeed in waiting for the
             * work to be done.
             */
//          INIT_WORK(&mddev->del_work, mddev_delayed_delete);
//          schedule_work(&mddev->del_work);
        } else
            free(mddev);
    }
}

static void mddev_init(mddev_t *mddev)
{
    INIT_LIST_HEAD(&mddev->disks);
    INIT_LIST_HEAD(&mddev->all_mddevs);
//  init_timer(&mddev->safemode_timer);
    atomic_set(&mddev->active, 1);
    atomic_set(&mddev->openers, 0);
//  atomic_set(&mddev->active_io, 0);
//  spin_lock_init(&mddev->write_lock);
//  atomic_set(&mddev->flush_pending, 0);
//  init_waitqueue_head(&mddev->sb_wait);
//  init_waitqueue_head(&mddev->recovery_wait);
//  mddev->reshape_position = MaxSector;
//  mddev->resync_min = 0;
//  mddev->resync_max = MaxSector;
//  mddev->level = LEVEL_NONE;

}

static inline mddev_t *mddev_get(mddev_t *mddev)
{
    (&mddev->active)->counter++;
    return mddev;
}

static mddev_t * mddev_find(dev_t unit)
{
    mddev_t *mddev, *new = NULL;

 retry:
    if (unit) {
        mddev = (mddev_t *) (&all_mddevs)->next;
        while (1) {
            prefetch(mddev->all_mddevs.next);
            if (&mddev->all_mddevs == (&all_mddevs)) {
                break;
            }
            if (mddev->unit == unit) {
                mddev_get(mddev);
                free(new);
                return mddev;
            }
            mddev = (mddev_t *) mddev->all_mddevs.next;
        }
        if (new) {
            list_add(&new->all_mddevs, &all_mddevs);
            new->hold_active = 1;
            return new;
        }
    } else if (new) {
        /* find an unused unit number */
        static int next_minor = 512;
        int start = next_minor;
        int is_free = 0;
        int dev = 0;
        while (!is_free) {
            dev = (((9) << 20) | (next_minor));
            next_minor++;
            if (next_minor > ((1U << 20) - 1))
                next_minor = 0;
            if (next_minor == start) {
                /* Oh dear, all in use. */
                free(new);
                return NULL;
            }

            is_free = 1;

            mddev = (mddev_t *) (&all_mddevs)->next;
            while (1) {
                prefetch(mddev->all_mddevs.next);
                if (&mddev->all_mddevs == (&all_mddevs)) {
                    break;
                }
                if (mddev->unit == dev) {
                    is_free = 0;
                    break;
                }
                mddev = (mddev_t *) mddev->all_mddevs.next;
            }
        }
        new->unit = dev;
        new->md_minor = ((unsigned int) ((dev) & ((1U << 20) - 1)));
        new->hold_active = 2;
        list_add(&new->all_mddevs, &all_mddevs);
        return new;
    }

    new = (mddev_t *) malloc (sizeof(mddev_t));
    if (!new)
        return NULL;

    new->unit = unit;
    if (((unsigned int) ((unit) >> 20)) == 9)
        new->md_minor = ((unsigned int) ((unit) & ((1U << 20) - 1)));
    else
        new->md_minor = ((unsigned int) ((unit) & ((1U << 20) - 1))) >> 6;

    mddev_init(new);

    goto retry;
}

static mdk_rdev_t * find_rdev_nr(mddev_t *mddev, int nr)
{
    mdk_rdev_t *rdev;

    rdev = (mdk_rdev_t *) (&mddev->disks)->next;
    while (1) {
        prefetch(rdev->same_set.next);
        if (&rdev->same_set == (&mddev->disks)) {
            break;
        }
        if (rdev->desc_nr == nr)
            return rdev;
        rdev = (mdk_rdev_t *) rdev->same_set.next;
    }

    return NULL;
}

static mdk_rdev_t * find_rdev(mddev_t * mddev, dev_t dev)
{
    mdk_rdev_t *rdev;

    rdev = (mdk_rdev_t *) (&mddev->disks)->next;
    while (1) {
        prefetch(rdev->same_set.next);
        if (&rdev->same_set == (&mddev->disks)) {
            break;
        }
        if (rdev->bdev->bd_dev == dev)
            return rdev;
        rdev = (mdk_rdev_t *) rdev->same_set.next;
    }

    return NULL;
}

static struct mdk_personality *find_pers(int level, char *clevel)
{
    struct mdk_personality *pers;

    pers = (struct mdk_personality *) (&pers_list)->next;
    while (1) {
        prefetch(pers->list.next);
        if (&pers->list == (&pers_list)) {
            break;
        }
        if (level != (-1000000) && pers->level == level)
            return pers;
        if (strcmp(pers->name, clevel)==0)
            return pers;
        pers = (struct mdk_personality *) pers->list.next;
    }

    return NULL;
}

static LIST_HEAD(pending_raid_disks);

/*
 * test bit
 */
static inline int test_bit(int nr, const volatile void *addr)
{
    return 1UL & (((const unsigned int *) addr)[nr >> 5] >> (nr & 31));
}

/*
 * Try to register data integrity profile for an mddev
 *
 * This is called when an array is started and after a disk has been kicked
 * from the array. It only succeeds if all working and active component devices
 * are integrity capable with matching profiles.
 */
int md_integrity_register(mddev_t *mddev)
{
    mdk_rdev_t *rdev, *reference = NULL;

    if (list_empty(&mddev->disks))
        return 0; /* nothing to do */
    if ((0))
        return 0;

    rdev = (mdk_rdev_t *) (&mddev->disks)->next;
    while (1) {
        prefetch(rdev->same_set.next);
        if (&rdev->same_set == (&mddev->disks)) {
            break;
        }
        /* skip spares and non-functional disks */
        if (test_bit(1, &rdev->flags))
            continue;
        if (rdev->raid_disk < 0)
            continue;
        /*
         * If at least one rdev is not integrity capable, we can not
         * enable data integrity for the md device.
         */
        if (!(0))
            return -22;
        if (!reference) {
            /* Use the first rdev as the reference */
            reference = rdev;
            continue;
        }
        /* does this rdev's profile match the reference profile? */
        if ((0) < 0)
            return -22;
        rdev = (mdk_rdev_t *) rdev->same_set.next;
    }

    /*
     * All component devices are integrity capable and have matching
     * profiles, register the common profile for the md device.
     */
    if ((0) != 0) {
        return -22;
    }
    return 0;
}

static void unbind_rdev_from_array(mdk_rdev_t * rdev)
{
    if (!rdev->mddev) {
        return;
    }
    bd_release_from_disk(rdev->bdev, rdev->mddev->gendisk);
    list_del_rcu(&rdev->same_set);
    rdev->mddev = NULL;
    sysfs_remove_link(&rdev->kobj, "block");
    sysfs_put(rdev->sysfs_state);
    rdev->sysfs_state = NULL;
//  INIT_WORK(&rdev->del_work, md_delayed_delete);
    kobject_get(&rdev->kobj);
//  schedule_work(&rdev->del_work);
}

static void super_90_sync(mddev_t *mddev, mdk_rdev_t *rdev)
{
    return;
}

static void super_1_sync(mddev_t *mddev, mdk_rdev_t *rdev)
{
    return;
}

static unsigned long long
super_90_rdev_size_change(mdk_rdev_t *rdev, sector_t num_sectors)
{
    return 0;
}

static unsigned long long
super_1_rdev_size_change(mdk_rdev_t *rdev, sector_t num_sectors)
{
    return 0;
}

/*
 * load_super for 0.90.0
 */
static int super_90_load(mdk_rdev_t *rdev, mdk_rdev_t *refdev, int minor_version)
{
    return 0;
}

static int super_1_load(mdk_rdev_t *rdev, mdk_rdev_t *refdev, int minor_version)
{
    return 0;
}

static struct super_type super_types[] = {
    [0] = {
        .name   = "0.90.0",
//      .owner  = THIS_MODULE,
        .load_super     = super_90_load,
//      .validate_super     = super_90_validate,
        .sync_super     = super_90_sync,
        .rdev_size_change   = super_90_rdev_size_change,
    },
    [1] = {
        .name   = "md-1",
//      .owner  = THIS_MODULE,
        .load_super     = super_1_load,
//      .validate_super     = super_1_validate,
        .sync_super     = super_1_sync,
        .rdev_size_change   = super_1_rdev_size_change,
    },
};

static void sync_sbs(mddev_t * mddev, int nospares)
{
    /* Update each superblock (in-memory image), but
     * if we are allowed to, skip spares which already
     * have the right event counter, or have one earlier
     * (which would mean they aren't being marked as dirty
     * with the rest of the array)
     */
    mdk_rdev_t *rdev;

    /* First make sure individual recovery_offsets are correct */
    rdev = (mdk_rdev_t *) (&mddev->disks)->next;
    while (1) {
        prefetch(rdev->same_set.next);
        if (&rdev->same_set == (&mddev->disks)) {
            break;
        }
        if (rdev->raid_disk >= 0 &&
            mddev->delta_disks >= 0 &&
            !test_bit(2, &rdev->flags) &&
            mddev->curr_resync_completed > rdev->recovery_offset)
                rdev->recovery_offset = mddev->curr_resync_completed;
        rdev = (mdk_rdev_t *) rdev->same_set.next;
    }

    rdev = (mdk_rdev_t *) (&mddev->disks)->next;
    while (1) {
        prefetch(rdev->same_set.next);
        if (&rdev->same_set == (&mddev->disks)) {
            break;
        }
        if (rdev->sb_events == mddev->events ||
            (nospares &&
             rdev->raid_disk < 0 &&
             rdev->sb_events+1 == mddev->events)) {
            /* Don't update this superblock */
            rdev->sb_loaded = 2;
        } else {
            super_types[mddev->major_version].
                sync_super(mddev, rdev);
            rdev->sb_loaded = 1;
        }
        rdev = (mdk_rdev_t *) rdev->same_set.next;
    }
}


static int strict_blocks_to_sectors(const char *buf, sector_t *sectors) {
    unsigned long long blocks;
    sector_t new;

    if (strict_strtoull(buf, 10, &blocks) < 0)
        return -22;

    if (blocks & 1ULL << (8 * sizeof(blocks) - 1))
        return -22; /* sector conversion overflow */

    new = blocks * 2;
    if (new != blocks * 2)
        return -22; /* unsigned long long to sector_t overflow */

    *sectors = new;
    return 0;
}

static int rdev_size_store(mdk_rdev_t *rdev, const char *buf, unsigned int len)
{
    mddev_t *my_mddev = rdev->mddev;
    sector_t oldsectors = rdev->sectors;
    sector_t sectors;

    if (strict_blocks_to_sectors(buf, &sectors) < 0)
        return -22;
    if (my_mddev->pers && rdev->raid_disk >= 0) {
        if (my_mddev->persistent) {
            sectors = super_types[my_mddev->major_version].
                rdev_size_change(rdev, sectors);
            if (!sectors)
                return -16;
        } else if (!sectors)
            sectors = (rdev->bdev->bd_inode->i_size >> 9) -
                rdev->data_offset;
    }
    if (sectors < my_mddev->dev_sectors)
        return -22; /* component must fit device */

    rdev->sectors = sectors;
    if (sectors > oldsectors && my_mddev->external) {
        /* need to check that all other rdevs with the same ->bdev
         * do not overlap.  We need to unlock the mddev to avoid
         * a deadlock.  We have already changed rdev->sectors, and if
         * we have to change it back, we will have the lock again.
         */
        mddev_t *mddev;
        int overlap = 0;
        struct list_head *tmp;


        tmp = all_mddevs.next;
        mddev = NULL;
        while (1){
            if (tmp != &all_mddevs)
                mddev_get((mddev_t *) tmp);
            if (mddev)
                mddev_put(mddev);
            mddev = mddev_get((mddev_t *) tmp);
            if (tmp == &all_mddevs){
                break;
            }
            mdk_rdev_t *rdev2;

            rdev2 = (mdk_rdev_t *) (&mddev->disks)->next;
            while (1){
                prefetch(rdev2->same_set.next);
                if (&rdev2->same_set == (&mddev->disks)) {
                    break;
                }
                if (test_bit(6, &rdev2->flags) ||
                    (rdev->bdev == rdev2->bdev &&
                     rdev != rdev2 &&
                     overlaps(rdev->data_offset, rdev->sectors,
                          rdev2->data_offset,
                          rdev2->sectors))) {
                    overlap = 1;
                    break;
                }
                rdev2 = (mdk_rdev_t *) rdev2->same_set.next;
            }
            if (overlap) {
                mddev_put(mddev);
                break;
            }
            tmp = tmp->next;
        }
        if (overlap) {
            /* Someone else could have slipped in a size
             * change here, but doing so is just silly.
             * We put oldsectors back because we *know* it is
             * safe, and trust userspace not to race with
             * itself
             */
            rdev->sectors = oldsectors;
            return -16;
        }
    }
    return len;
}

/*
 * Import a device. If 'super_format' >= 0, then sanity check the superblock
 *
 * mark the device faulty if:
 *
 *   - the device is nonexistent (zero size)
 *   - the device has no valid superblock
 *
 * a faulty rdev _never_ has rdev->sb set.
 */
static mdk_rdev_t *md_import_device(dev_t newdev, int super_format, int super_minor)
{
    int err;
    mdk_rdev_t *rdev;
    sector_t size;

    rdev = (mdk_rdev_t *) malloc(sizeof(mdk_rdev_t));
    if (!rdev) {
        return ERR_PTR(-12);
    }

    if ((err = alloc_disk_sb(rdev)))
        goto abort_free;

    err = lock_rdev(rdev, newdev, super_format == -2);
    if (err)
        goto abort_free;

//  kobject_init(&rdev->kobj, &rdev_ktype);

    rdev->desc_nr = -1;
    rdev->saved_raid_disk = -1;
    rdev->raid_disk = -1;
    rdev->flags = 0;
    rdev->data_offset = 0;
    rdev->sb_events = 0;
//  rdev->last_read_error.tv_sec  = 0;
//  rdev->last_read_error.tv_nsec = 0;
    atomic_set(&rdev->nr_pending, 0);
    atomic_set(&rdev->read_errors, 0);
    atomic_set(&rdev->corrected_errors, 0);

    size = rdev->bdev->bd_inode->i_size >> 10;
    if (!size) {
        err = -22;
        goto abort_free;
    }

    if (super_format >= 0) {
        err = super_types[super_format].
            load_super(rdev, NULL, super_minor);
        if (err == -22) {
            goto abort_free;
        }
        if (err < 0) {
            goto abort_free;
        }
    }

    INIT_LIST_HEAD(&rdev->same_set);

    return rdev;

abort_free:
    if (rdev->sb_page) {
        if (rdev->bdev)
            unlock_rdev(rdev);
        free_disk_sb(rdev);
    }
    free(rdev);
    return ERR_PTR(err);
}

/* mode:
 *   0 - completely stop and dis-assemble array
 *   2 - stop but do not disassemble array
 */
static int do_md_stop(mddev_t * mddev, int mode, int is_open)
{
    int err = 0;
    struct gendisk *disk = mddev->gendisk;
    mdk_rdev_t *rdev;

    if (atomic_read(&mddev->openers) > is_open) {
        err = -16;
    }
    else if (mddev->pers) {

        if (mddev->ro)
            set_disk_ro(disk, 0);

        md_stop(mddev);
//      mddev->queue->merge_bvec_fn = NULL;
//      mddev->queue->unplug_fn = NULL;
//      mddev->queue->backing_dev_info.congested_fn = NULL;

        /* tell userspace to handle 'inactive' */
        sysfs_notify_dirent(mddev->sysfs_state);

        rdev = (mdk_rdev_t *) (&mddev->disks)->next;
        while (1) {
            prefetch(rdev->same_set.next);
            if (&rdev->same_set == (&mddev->disks)) {
                break;
            }
            if (rdev->raid_disk >= 0) {
                char nm[20];
                sysfs_remove_link(&mddev->kobj, nm);
            }
            rdev = (mdk_rdev_t *) rdev->same_set.next;
        }

        set_capacity(disk, 0);
        revalidate_disk(disk);

        if (mddev->ro)
            mddev->ro = 0;

        err = 0;
    }
    if (err)
        return err;
    /*
     * Free resources if final stop
     */
    if (mode == 0) {


//      bitmap_destroy(mddev);
//      if (mddev->bitmap_info.file) {
//          restore_bitmap_write_access(mddev->bitmap_info.file);
//          fput(mddev->bitmap_info.file);
//          mddev->bitmap_info.file = NULL;
//      }
//      mddev->bitmap_info.offset = 0;
//
//      export_array(mddev);
//
//      md_clean(mddev);
//      kobject_uevent(&disk_to_dev(mddev->gendisk)->kobj, KOBJ_CHANGE);
//      if (mddev->hold_active == UNTIL_STOP)
//          mddev->hold_active = 0;

    }
    err = 0;
    blk_integrity_unregister(disk);
    md_new_event(mddev);
    sysfs_notify_dirent(mddev->sysfs_state);
    return err;
}

static int update_size(mddev_t *mddev, sector_t num_sectors)
{
    mdk_rdev_t *rdev;
    int rv;
    int fit = (num_sectors == 0);

//  if (mddev->pers->resize == NULL)
//      return -22;
    /* The "num_sectors" is the number of sectors of each device that
     * is used.  This can only make sense for arrays with redundancy.
     * linear and raid0 always use whatever space is available. We can only
     * consider changing this number if no resync or reconstruction is
     * happening, and if the new size is acceptable. It must fit before the
     * sb_start or, if that is <data_offset, it must fit before the size
     * of each device.  If num_sectors is zero, we find the largest size
     * that fits.

     */
//  if (mddev->sync_thread)
//      return -16;
//  if (mddev->bitmap)
//      /* Sorry, cannot grow a bitmap yet, just remove it,
//       * grow, and re-add.
//       */
//      return -16;

    rdev = (mdk_rdev_t *) (&mddev->disks)->next;
    while (1) {
        prefetch(rdev->same_set.next);
        if (&rdev->same_set == (&mddev->disks)) {
            break;
        }
        sector_t avail = rdev->sectors;

        if (fit && (num_sectors == 0 || num_sectors > avail))
            num_sectors = avail;
        if (avail < num_sectors)
            return -28;
        rdev = (mdk_rdev_t *) rdev->same_set.next;
    }

//  rv = mddev->pers->resize(mddev, num_sectors);
    if (!rv)
        revalidate_disk(mddev->gendisk);
    return rv;
}

static void *md_seq_start(struct seq_file *seq, long long *pos) {
    struct list_head *tmp;
    long long l = *pos;
    mddev_t *mddev;

    if (l >= 0x10000)
        return NULL;
    if (!l--)
        /* header */
        return (void*) 1;

    for (tmp = (&all_mddevs)->next; prefetch(tmp->next), tmp != (&all_mddevs); tmp= tmp->next) {
        if (!l--) {
            mddev = (mddev_t *) tmp;
            mddev_get(mddev);
            return mddev;
        }
    }
    if (!l--)
        return (void*) 2;/* tail */
    return NULL;
}

static int remove_and_add_spares(mddev_t *mddev)
{
    mdk_rdev_t *rdev;
    int spares = 0;

    mddev->curr_resync_completed = 0;

    rdev = (mdk_rdev_t *) (&mddev->disks)->next;
    while (1) {
        prefetch(rdev->same_set.next);
        if (&rdev->same_set == (&mddev->disks)) {
            break;
        }
        if (rdev->raid_disk >= 0 &&
            !test_bit(8, &rdev->flags) &&
            (test_bit(1, &rdev->flags) ||
             ! test_bit(2, &rdev->flags)) &&
            atomic_read(&rdev->nr_pending)==0) {
//          if (mddev->pers->hot_remove_disk(
//                  mddev, rdev->raid_disk)==0) {
//              char nm[20];
//              sysfs_remove_link(&mddev->kobj, nm);
//              rdev->raid_disk = -1;
//          }
        }
        rdev = (mdk_rdev_t *) rdev->same_set.next;
    }

    if (mddev->degraded && ! mddev->ro && !mddev->recovery_disabled) {
        rdev = (mdk_rdev_t *) (&mddev->disks)->next;
        while (1) {
            prefetch(rdev->same_set.next);
            if (&rdev->same_set == (&mddev->disks)) {
                break;
            }
            if (rdev->raid_disk >= 0 &&
                !test_bit(2, &rdev->flags) &&
                !test_bit(8, &rdev->flags))
                spares++;
            if (rdev->raid_disk < 0
                && !test_bit(1, &rdev->flags)) {
                rdev->recovery_offset = 0;
//              if (mddev->pers->hot_add_disk(mddev, rdev) == 0) {
//                  char nm[20];
//                  if (sysfs_create_link(&mddev->kobj,
//                                &rdev->kobj, nm))
//                  spares++;
//                  md_new_event(mddev);
//                  set_bit(MD_CHANGE_DEVS, &mddev->flags);
//              } else
//                  break;
            }
            rdev = (mdk_rdev_t *) rdev->same_set.next;
        }
    }
    return spares;
}

void md_autodetect_dev(dev_t dev)
{
    struct detected_devices_node *node_detected_dev;

    node_detected_dev = (struct detected_devices_node *) malloc (sizeof(struct detected_devices_node));
    if (node_detected_dev) {
        node_detected_dev->dev = dev;
        list_add_tail(&node_detected_dev->list, &all_detected_devices);
    }
}

static void autostart_arrays(int part)
{
    mdk_rdev_t *rdev;
    struct detected_devices_node *node_detected_dev;
    dev_t dev;
    int i_scanned, i_passed;

    i_scanned = 0;
    i_passed = 0;

    while (!list_empty(&all_detected_devices) && i_scanned < 0x7fffffff) {
        i_scanned++;
        node_detected_dev = (struct detected_devices_node *) all_detected_devices.next;
        list_del(&node_detected_dev->list);
        dev = node_detected_dev->dev;
        free(node_detected_dev);
        rdev = md_import_device(dev,0, 90);
        if (IS_ERR(rdev))
            continue;

        if (test_bit(1, &rdev->flags)) {
            continue;
        }
        set_bit(7, &rdev->flags);
        list_add(&rdev->same_set, &pending_raid_disks);
        i_passed++;
    }
    autorun_devices(part);
}


int main(void)
{
    return 0;
}

