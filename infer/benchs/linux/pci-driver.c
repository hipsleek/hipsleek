/*
 * drivers/pci/pci-driver.c
 *
 * (C) Copyright 2002-2004, 2007 Greg Kroah-Hartman <greg@kroah.com>
 * (C) Copyright 2007 Novell Inc.
 *
 * Released under the GPL v2 only.
 *
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

/****************************************************************************/

struct pci_device_id {
    unsigned int vendor, device; /* Vendor and device ID or PCI_ANY_ID*/
    unsigned int subvendor, subdevice; /* Subsystem ID's or PCI_ANY_ID */
    unsigned int class, class_mask; /* (class,subclass,prog-if) triplet */
    unsigned long int driver_data; /* Data private to the driver */
};

struct pci_dynid {
    struct list_head node;
    struct pci_device_id id;
};

struct pci_dynids {
    struct list_head list;
};

struct bus_type {
    const char *name;

//  struct bus_attribute *bus_attrs;
//  struct device_attribute *dev_attrs;
//  struct driver_attribute *drv_attrs;
//
//  int (*match)(struct device *dev, struct device_driver *drv);
//  int (*uevent)(struct device *dev, struct kobj_uevent_env *env);
//  int (*probe)(struct device *dev);
//  int (*remove)(struct device *dev);
//  void (*shutdown)(struct device *dev);
//
//  int (*suspend)(struct device *dev, pm_message_t state);
//  int (*resume)(struct device *dev);
//
//  const struct dev_pm_ops *pm;
//
//  struct bus_type_private *p;
};

struct module {
    struct module *next;
    const char *name;
//  int gpl_compatible;
//  struct symbol *unres;
//  int seen;
//  int skip;
//  int has_init;
//  int has_cleanup;
//  struct buffer dev_table_buf;
//  char         srcversion[25];
};

struct device_driver {
    const char *name;
    struct bus_type *bus;

    struct module *owner;
    const char *mod_name;

//  bool suppress_bind_attrs;
//  int (*probe) (struct device *dev);
//  int (*remove) (struct device *dev);
//  void (*shutdown) (struct device *dev);
//  int (*suspend) (struct device *dev, pm_message_t state);
//  int (*resume) (struct device *dev);
//  const struct attribute_group **groups;
//  const struct dev_pm_ops *pm;
//  struct driver_private *p;
};

struct pci_driver {
    struct list_head node;
    char *name;
    const struct pci_device_id *id_table;
//  int (*probe) (struct pci_dev *dev, const struct pci_device_id *id);
//  void (*remove) (struct pci_dev *dev);
//  int (*suspend) (struct pci_dev *dev, pm_message_t state);
//  int (*suspend_late) (struct pci_dev *dev, pm_message_t state);
//  int (*resume_early) (struct pci_dev *dev);
//  int (*resume) (struct pci_dev *dev);
//  void (*shutdown) (struct pci_dev *dev);
//  struct pci_error_handlers *err_handler;
    struct device_driver driver;
    struct pci_dynids dynids;
};

struct pci_dev {
//  struct list_head bus_list;
//  struct pci_bus *bus;
//  struct pci_bus *subordinate;
//  void *sysdata;
//  struct proc_dir_entry *procent;
//  struct pci_slot *slot;
//  unsigned int devfn;
    unsigned short vendor;
    unsigned short device;
    unsigned short subsystem_vendor;
    unsigned short subsystem_device;
    unsigned int class;
//  u8 revision;
//  u8 hdr_type;
//  u8 pcie_cap;
//  u8 pcie_type;
//  u8 rom_base_reg;
//  u8 pin;
//  struct pci_driver *driver;
//  u64 dma_mask;
//  struct device_dma_parameters dma_parms;
//  pci_power_t current_state;
//  int pm_cap;
//  unsigned int pme_support:5;
//  unsigned int pme_interrupt:1;
//  unsigned int d1_support:1;
//  unsigned int d2_support:1;
//  unsigned int no_d1d2:1;
//  unsigned int wakeup_prepared:1;
//  unsigned int d3_delay;
//  pci_channel_state_t error_state;
//  struct device dev;
//  int cfg_size;
//  unsigned int irq;
//  struct resource resource[DEVICE_COUNT_RESOURCE];
//  resource_size_t fw_addr[DEVICE_COUNT_RESOURCE];
//  unsigned int transparent:1;
//  unsigned int multifunction:1;
//  unsigned int is_added:1;
//  unsigned int is_busmaster:1;
//  unsigned int no_msi:1;
//  unsigned int block_ucfg_access:1;
//  unsigned int broken_parity_status:1;
//  unsigned int irq_reroute_variant:2;
//  unsigned int msi_enabled:1;
//  unsigned int msix_enabled:1;
//  unsigned int ari_enabled:1;
//  unsigned int is_managed:1;
//  unsigned int is_pcie:1;
//  unsigned int needs_freset:1;
//  unsigned int state_saved:1;
//  unsigned int is_physfn:1;
//  unsigned int is_virtfn:1;
//  unsigned int reset_fn:1;
//  unsigned int is_hotplug_bridge:1;
//  unsigned int __aer_firmware_first_valid:1;
//  unsigned int __aer_firmware_first:1;
//  pci_dev_flags_t dev_flags;
//  atomic_t enable_cnt;
//  u32 saved_config_space[16];
//  struct hlist_head saved_cap_space;
//  struct bin_attribute *rom_attr;
//  int rom_attr_enabled;
//  struct bin_attribute *res_attr[DEVICE_COUNT_RESOURCE];
//  struct bin_attribute *res_attr_wc[DEVICE_COUNT_RESOURCE];
//  struct pci_vpd *vpd;
};

struct bus_type pci_bus_type = {
    .name       = "pci",
//  .match      = pci_bus_match,
//  .uevent     = pci_uevent,
//  .probe      = pci_device_probe,
//  .remove     = pci_device_remove,
//  .shutdown   = pci_device_shutdown,
//  .dev_attrs  = pci_dev_attrs,
//  .bus_attrs  = pci_bus_attrs,
//  .pm     = PCI_PM_OPS_PTR,
};

struct device {
    struct device       *parent;

//  struct device_private   *p;
//
//  struct kobject kobj;
//  const char      *init_name; /* initial name of the device */
//  struct device_type  *type;
//
//  struct mutex        mutex;  /* mutex to synchronize calls to
//                   * its driver.
//                   */
//
//  struct bus_type *bus;       /* type of bus device is on */
//  struct device_driver *driver;   /* which driver has allocated this
//                     device */
//  void        *platform_data; /* Platform specific data, device
//                     core doesn't touch it */
//  struct dev_pm_info  power;
//
//#ifdef CONFIG_NUMA
//  int     numa_node;  /* NUMA node this device is close to */
//#endif
//  u64     *dma_mask;  /* dma mask (if dma'able device) */
//  u64     coherent_dma_mask;/* Like dma_mask, but for
//                       alloc_coherent mappings as
//                       not all hardware supports
//                       64 bit addresses for consistent
//                       allocations such descriptors. */
//
//  struct device_dma_parameters *dma_parms;
//
//  struct list_head    dma_pools;  /* dma pools (if dma'ble) */
//
//  struct dma_coherent_mem *dma_mem; /* internal for coherent mem
//                       override */
//  /* arch specific additions */
//  struct dev_archdata archdata;
//#ifdef CONFIG_OF
//  struct device_node  *of_node;
//#endif
//
//  dev_t           devt;   /* dev_t, creates the sysfs "dev" */
//
//  spinlock_t      devres_lock;
//  struct list_head    devres_head;
//
//  struct klist_node   knode_class;
//  struct class        *class;
//  const struct attribute_group **groups;  /* optional groups */
//
//  void    (*release)(struct device *dev);
};


/****************************************************************************/

/**
 * get_driver - increment driver reference count.
 * @drv: driver.
 */
struct device_driver *get_driver(struct device_driver *drv) {
    struct device_driver *a;
    return a;
}
/**
 * put_driver - decrement driver's refcount.
 * @drv: driver.
 */
void put_driver(struct device_driver *drv) {
    return;
}

/**
 * driver_attach - try to bind driver to devices.
 * @drv: driver.
 *
 * Walk the list of devices that the bus has on it and try to
 * match the driver with each one.  If driver_probe_device()
 * returns 0 and the @dev->driver is set, we've found a
 * compatible pair.
 */
int driver_attach(struct device_driver *drv) {
    return 0;
}

void prefetch(void *x)
{
    return;
}

/**
 * driver_register - register driver with bus
 * @drv: driver to register
 *
 * We pass off most of the work to the bus_add_driver() call,
 * since most of the things we have to do deal with the bus
 * structures.
 */
int driver_register(struct device_driver *drv )
{
    int a;
    return a;
}

/**
 * driver_unregister - remove driver from system.
 * @drv: driver.
 *
 * Again, we pass off most of the work to the bus-level call.
 */
void driver_unregister(struct device_driver *drv) {
    return;
}
/****************************************************************************/

/**
 * pci_match_one_device - Tell if a PCI device structure has a matching
 *                        PCI device id structure
 * @id: single PCI device id structure to match
 * @dev: the PCI device structure to match against
 *
 * Returns the matching pci_device_id structure or %NULL if there is no match.
 */
static inline const struct pci_device_id *
pci_match_one_device(const struct pci_device_id *id, const struct pci_dev *dev)
{
    if ((id->vendor == (~0) || id->vendor == dev->vendor) &&
        (id->device == (~0) || id->device == dev->device) &&
        (id->subvendor == (~0) || id->subvendor == dev->subsystem_vendor) &&
        (id->subdevice == (~0) || id->subdevice == dev->subsystem_device) &&
        !((id->class ^ dev->class) & id->class_mask))
        return id;
    return NULL;
}
/****************************************************************************/

/**
 * pci_add_dynid - add a new PCI device ID to this driver and re-probe devices
 * @drv: target pci driver
 * @vendor: PCI vendor ID
 * @device: PCI device ID
 * @subvendor: PCI subvendor ID
 * @subdevice: PCI subdevice ID
 * @class: PCI class
 * @class_mask: PCI class mask
 * @driver_data: private driver data
 *
 * Adds a new dynamic pci device ID to this driver and causes the
 * driver to probe for all devices again.  @drv must have been
 * registered prior to calling this function.
 *
 * CONTEXT:
 * Does GFP_KERNEL allocation.
 *
 * RETURNS:
 * 0 on success, -errno on failure.
 */
int pci_add_dynid(struct pci_driver *drv,
          unsigned int vendor, unsigned int device,
          unsigned int subvendor, unsigned int subdevice,
          unsigned int class, unsigned int class_mask,
          unsigned long driver_data)
{
    struct pci_dynid *dynid;
    int retval;

    dynid = (struct pci_dynid *) malloc(sizeof(struct pci_dynid));
    if (!dynid)
        return -12;

    dynid->id.vendor = vendor;
    dynid->id.device = device;
    dynid->id.subvendor = subvendor;
    dynid->id.subdevice = subdevice;
    dynid->id.class = class;
    dynid->id.class_mask = class_mask;
    dynid->id.driver_data = driver_data;

    list_add_tail(&dynid->node, &drv->dynids.list);

    get_driver(&drv->driver);
    retval = driver_attach(&drv->driver);
    put_driver(&drv->driver);

    return retval;
}

static void pci_free_dynids(struct pci_driver *drv)
{
    struct pci_dynid *dynid, *n;

    dynid = (struct pci_dynid *) (&drv->dynids.list)->next;
    n = (struct pci_dynid *) dynid->node.next;
    while (&dynid->node != (&drv->dynids.list)) {
        list_del(&dynid->node);
        free(dynid);
        dynid = n;
        n = (struct pci_dynid *) n->node.next;
    }
    return;
}

/**
 * store_remove_id - remove a PCI device ID from this driver
 * @driver: target device driver
 * @buf: buffer for scanning device ID data
 * @count: input size
 *
 * Removes a dynamic pci device ID to this driver.
 */
static int
store_remove_id(struct device_driver *driver, const char *buf, int count)
{
    struct pci_dynid *dynid, *n;
    struct pci_driver *pdrv = (struct pci_driver *) driver;
    unsigned int vendor,
    device,
    subvendor = (~0),
    subdevice = (~0),
    class = 0,
    class_mask = 0;
    int fields = 0;
    int retval = -19;

    fields = sscanf(buf, "%x %x %x %x %x %x",
            &vendor, &device, &subvendor, &subdevice,
            &class, &class_mask);
    if (fields < 2)
        return -22;

    dynid = (struct pci_dynid *) (&pdrv->dynids.list)->next;
    n = (struct pci_dynid *) dynid->node.next;
    while (&dynid->node != (&pdrv->dynids.list)){
        struct pci_device_id *id = &dynid->id;
        if ((id->vendor == vendor) &&
            (id->device == device) &&
            (subvendor == (~0) || id->subvendor == subvendor) &&
            (subdevice == (~0) || id->subdevice == subdevice) &&
            !((id->class ^ class) & class_mask)) {
            list_del(&dynid->node);
            free(dynid);
            retval = 0;
            break;
        }
        dynid = n;
        n = (struct pci_dynid *) n->node.next;
    }

    if (retval)
        return retval;
    return count;
}

/**
 * pci_match_id - See if a pci device matches a given pci_id table
 * @ids: array of PCI device id structures to search in
 * @dev: the PCI device structure to match against.
 *
 * Used by a driver to check whether a PCI device present in the
 * system is in its list of supported devices.  Returns the matching
 * pci_device_id structure or %NULL if there is no match.
 *
 * Deprecated, don't use this as it will not catch any dynamic ids
 * that a driver might want to check for.
 */
const struct pci_device_id *pci_match_id(const struct pci_device_id *ids,
                     struct pci_dev *dev)
{
    if (ids) {
        while (ids->vendor || ids->subvendor || ids->class_mask) {
            if (pci_match_one_device(ids, dev))
                return ids;
            ids++;
        }
    }
    return NULL;
}

/**
 * pci_match_device - Tell if a PCI device structure has a matching PCI device id structure
 * @drv: the PCI driver to match against
 * @dev: the PCI device structure to match against
 *
 * Used by a driver to check whether a PCI device present in the
 * system is in its list of supported devices.  Returns the matching
 * pci_device_id structure or %NULL if there is no match.
 */
static const struct pci_device_id *pci_match_device(struct pci_driver *drv,
                            struct pci_dev *dev)
{
    struct pci_dynid *dynid;

    /* Look at the dynamic ids first, before the static ones */
    dynid = (struct pci_dynid *) (&drv->dynids.list)->next;
    while (1) {
        prefetch((void *) dynid->node.next);
        if (&dynid->node == (&drv->dynids.list)){
            break;
        }
        if (pci_match_one_device(&dynid->id, dev)) {
            return &dynid->id;
        }
        dynid = (struct pci_dynid *) dynid->node.next;
    }
    return pci_match_id(drv->id_table, dev);
}

static inline int pci_create_newid_file(struct pci_driver *drv)
{
    return 0;
}

static inline int pci_create_removeid_file(struct pci_driver *drv)
{
    return 0;
}

static inline void pci_remove_newid_file(struct pci_driver *drv) {}

/**
 * __pci_register_driver - register a new pci driver
 * @drv: the driver structure to register
 * @owner: owner module of drv
 * @mod_name: module name string
 *
 * Adds the driver structure to the list of registered drivers.
 * Returns a negative value on error, otherwise 0.
 * If no error occurred, the driver remains registered even if
 * no device was claimed during registration.
 */
int __pci_register_driver(struct pci_driver *drv, struct module *owner,
              const char *mod_name)
{
    int error;

    /* initialize common driver fields */
    drv->driver.name = drv->name;
    drv->driver.bus = &pci_bus_type;
    drv->driver.owner = owner;
    drv->driver.mod_name = mod_name;

    INIT_LIST_HEAD(&drv->dynids.list);

    /* register with core */
    error = driver_register(&drv->driver);
    if (error)
        goto out;

    error = pci_create_newid_file(drv);
    if (error)
        goto out_newid;

    error = pci_create_removeid_file(drv);
    if (error)
        goto out_removeid;

out:
    return error;

out_removeid:
    pci_remove_newid_file(drv);
out_newid:
    driver_unregister(&drv->driver);
    goto out;
}

static inline void pci_remove_removeid_file(struct pci_driver *drv) {}

/**
 * pci_unregister_driver - unregister a pci driver
 * @drv: the driver structure to unregister
 *
 * Deletes the driver structure from the list of registered PCI drivers,
 * gives it a chance to clean up by calling its remove() function for
 * each device it was responsible for, and marks those devices as
 * driverless.
 */

void
pci_unregister_driver(struct pci_driver *drv)
{
    pci_remove_removeid_file(drv);
    pci_remove_newid_file(drv);
    driver_unregister(&drv->driver);
    pci_free_dynids(drv);
}

/**
 * pci_bus_match - Tell if a PCI device structure has a matching PCI device id structure
 * @dev: the PCI device structure to match against
 * @drv: the device driver to search for matching PCI device id structures
 *
 * Used by a driver to check whether a PCI device present in the
 * system is in its list of supported devices. Returns the matching
 * pci_device_id structure or %NULL if there is no match.
 */
static int pci_bus_match(struct device *dev, struct device_driver *drv)
{
    struct pci_dev *pci_dev = (struct pci_dev *) dev;
    struct pci_driver *pci_drv = (struct pci_driver *) drv;
    const struct pci_device_id *found_id;

    found_id = pci_match_device(pci_drv, pci_dev);
    if (found_id)
        return 1;

    return 0;
}

int main(void)
{
    return 0;
}
