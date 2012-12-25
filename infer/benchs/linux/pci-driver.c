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
    entry->next = NULL;
    entry->prev = NULL;
}

/****************************************************************************/

struct pci_device_id {
    unsigned int vendor, device; /* Vendor and device ID or PCI_ANY_ID*/
    unsigned int subvendor, subdevice; /* Subsystem ID's or PCI_ANY_ID */
    unsigned int class, class_mask; /* (class,subclass,prog-if) triplet */
    unsigned long driver_data; /* Data private to the driver */
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
    //  int (*probe)(struct device *dev);
    //  int (*remove)(struct device *dev);
};

struct device_driver {
    const char *name;
    struct bus_type *bus;
    //  int (*probe)(struct device *dev);
    //  int (*remove)(struct device *dev);
};

struct pci_driver {
    struct list_head node;
    char *name;
    const struct pci_device_id *id_table;
    //  int (*probe)(struct pci_dev *dev, const struct pci_device_id *id);
    //  void (*remove)(struct pci_dev *dev);
    struct device_driver driver;
    struct pci_dynids dynids;
};

/****************************************************************************/

/**
 * get_driver - increment driver reference count.
 * @drv: driver.
 */
struct device_driver *get_driver(struct device_driver *drv) {
    if (drv) {
        struct device_driver *a;
        return a;
    }
    return NULL;
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
int pci_add_dynid(struct pci_driver *drv, unsigned int vendor,
        unsigned int device, unsigned int subvendor, unsigned int subdevice,
        unsigned int class, unsigned int class_mask, unsigned long driver_data) {
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
static int store_remove_id(struct device_driver *driver, const char *buf, int count)
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

int main(void)
{
    return 0;
}
