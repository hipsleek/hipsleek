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
    entry->next = NULL;
    entry->prev = NULL;
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

struct gendisk {
// int major;
// int first_minor;
// int minors;
//
//
// char disk_name[32];
// char *(*devnode)(struct gendisk *gd, mode_t *mode);
//
// struct disk_part_tbl *part_tbl;
// struct hd_struct part0;
//
// const struct block_device_operations *fops;
// struct request_queue *queue;
// void *private_data;
//
// int flags;
// struct device *driverfs_dev;
// struct kobject *slave_dir;
//
// struct timer_rand_state *random;
//
// atomic_t sync_io;
// struct work_struct async_notify;
// int node_id;
};

struct mddev_s
{
//  void                *private;
//  struct mdk_personality      *pers;
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
//  int             ro;
//
    struct gendisk          *gendisk;
//
//  struct kobject          kobj;
    int             hold_active;
//#define   UNTIL_IOCTL 1
//#define   UNTIL_STOP  2
//
//  /* Superblock information */
//  int             major_version,
//                  minor_version,
//                  patch_version;
//  int             persistent;
//  int                 external;   /* metadata is
//                           * managed externally */
//  char                metadata_type[17]; /* externally set*/
//  int             chunk_sectors;
//  time_t              ctime, utime;
//  int             level, layout;
//  char                clevel[16];
    int             raid_disks;
//  int             max_disks;
//  sector_t            dev_sectors;    /* used size of
//                           * component devices */
//  sector_t            array_sectors; /* exported array size */
//  int             external_size; /* size managed
//                          * externally */
//  __u64               events;
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
//  int             delta_disks, new_level, new_layout;
//  int             new_chunk_sectors;
//
//  struct mdk_thread_s     *thread;    /* management thread */
//  struct mdk_thread_s     *sync_thread;   /* doing resync or reconstruct */
//  sector_t            curr_resync;    /* last block scheduled */
//  /* As resync requests can complete out of order, we cannot easily track
//   * how much resync has been completed.  So we occasionally pause until
//   * everything completes, then set curr_resync_completed to curr_resync.
//   * As such it may be well behind the real resync mark, but it is a value
//   * we are certain of.
//   */
//  sector_t            curr_resync_completed;
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
//  int             recovery_disabled; /* if we detect that recovery
//                              * will always fail, set this
//                              * so we don't loop trying */
//
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
//  atomic_t            openers;    /* number of active opens */
//
//  int             degraded;   /* whether md should consider
//                           * adding a spare
//                           */
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
//  struct sysfs_dirent     *sysfs_state;   /* handle for 'array_state'
//                           * file in sysfs.
//                           */
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

struct block_device {
    dev_t bd_dev;
//  struct inode * bd_inode;
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

/*
 * MD's 'extended' device
 */
struct mdk_rdev_s
{
    struct list_head same_set;  /* RAID devices within the same set */

//  sector_t sectors;       /* Device size (in 512bytes sectors) */
//  mddev_t *mddev;         /* RAID array if running */
//  int last_events;        /* IO event timestamp */
//
    struct block_device *bdev;  /* block device handle */
//
//  struct page *sb_page;
//  int     sb_loaded;
//  __u64       sb_events;
//  sector_t    data_offset;    /* start of data in array */
//  sector_t    sb_start;   /* offset of the super block (in 512byte sectors) */
//  int     sb_size;    /* bytes in the superblock */
//  int     preferred_minor;    /* autorun support */
//
//  struct kobject  kobj;
//
//  /* A device can be in one of three states based on two flags:
//   * Not working:   faulty==1 in_sync==0
//   * Fully working: faulty==0 in_sync==1
//   * Working, but not
//   * in sync with array
//   *                faulty==0 in_sync==0
//   *
//   * It can never have faulty==1, in_sync==1
//   * This reduces the burden of testing multiple flags in many cases
//   */
//
//  unsigned long   flags;
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
//  int saved_raid_disk;        /* role that device used to have in the
//                   * array and could again if we did a partial
//                   * resync from the bitmap
//                   */
//  sector_t    recovery_offset;/* If this device has been partially
//                   * recovered, this is where we were
//                   * up to.
//                   */
//
//  atomic_t    nr_pending; /* number of pending requests.
//                   * only maintained for arrays that
//                   * support hot removal
//                   */
//  atomic_t    read_errors;    /* number of consecutive read errors that
//                   * we have tried to ignore.
//                   */
//  struct timespec last_read_error;    /* monotonic time since our
//                       * last read error
//                       */
//  atomic_t    corrected_errors; /* number of corrected read errors,
//                     * for reporting to userspace and storing
//                     * in superblock.
//                     */
//  struct work_struct del_work;    /* used for delayed sysfs removal */
//
//  struct sysfs_dirent *sysfs_state; /* handle for 'state'
//                     * sysfs entry */
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

typedef struct mddev_s mddev_t;
typedef struct mdk_rdev_s mdk_rdev_t;

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

/****************************************************************************/

static void mddev_put(mddev_t *mddev)
{
    if (!mddev->raid_disks && list_empty(&mddev->disks) &&
        !mddev->hold_active) {
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


