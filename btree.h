#include <cassert>
#include <climits>
#include <fstream>
#include <future>
#include <iostream>
#include <atomic>
#include <libpmemobj.h>
#include <math.h>
#include <mutex>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <time.h>
#include <unistd.h>
#include <vector>
#include "nodepref.h"

#define USE_PMDK
#define lazy_entry 3
#define NodeSIZE 1024
#define CACHE_LINE_SIZE 64 
#define IS_FORWARD(c) (c % 2 == 0)
extern long splitnum;
extern long clwbnum;
extern long sfencenum;
extern long alloer;
extern long Ialloer;
thread_local int work_id=-1;
using entry_key_t = int64_t;
//typedef unsigned int version_t;
//pthread_mutex_t print_mtx;

const uint64_t SPACE_PER_THREAD = 35ULL * 1024ULL * 1024ULL * 1024ULL;
const uint64_t SPACE_OF_MAIN_THREAD = 35ULL * 1024ULL * 1024ULL * 1024ULL;
extern __thread char *start_addr;
extern __thread char *curr_addr;

using namespace std;

#define bitScan(x)  __builtin_ffs(x) //return the 1 location in the end of x,from 0 to n
#define countBit(x) __builtin_popcount(x) //return the number of bit 1

inline void mfence()
{
  asm volatile("mfence":::"memory");
}

inline void clflush(void *data, int len)
{
  volatile char *ptr = (char *)((unsigned long)data &~(CACHE_LINE_SIZE-1));
  for(; ptr<data+len; ptr+=CACHE_LINE_SIZE){
    asm volatile(".byte 0x66; clflush %0" : "+m" (*((volatile char *)ptr)));
  }
  mfence();
}

//flush key from end to begin
inline void insclflushmore(void* end, void* begin)
{
    volatile char* bptr = (char*)((unsigned long)begin & ~(CACHE_LINE_SIZE - 1));
    volatile char* eptr = (char*)((unsigned long)end & ~(CACHE_LINE_SIZE - 1));
    //volatile int len = (bptr - eptr) / 4;
    for (; eptr >= bptr; eptr = eptr - CACHE_LINE_SIZE) {
        asm volatile(".byte 0x66; clflush %0" : "+m" (*((volatile char*)eptr)));
    }
    mfence();
}

//flush key from begin to end
inline void delclflushmore(void* begin, void* end)
{
    volatile char* bptr = (char*)((unsigned long)begin & ~(CACHE_LINE_SIZE - 1));
    volatile char* eptr = (char*)((unsigned long)end & ~(CACHE_LINE_SIZE - 1));
    //volatile int len = (bptr - eptr) / 4;

    for (; bptr <= eptr; bptr += CACHE_LINE_SIZE) {
        asm volatile(".byte 0x66; clflush %0" : "+m" (*((volatile char*)bptr)));
        
    }
    mfence();
}


/**
 * Pointer8B defines a class that can be assigned to either internal node or leaf node.
 */
class Pointer8B {
public:
    unsigned long long  value;  /* 8B to contain a pointer */

public:
    Pointer8B() {}

    Pointer8B(const void* ptr)
    {
        value = (unsigned long long)ptr;
    }

    Pointer8B(const Pointer8B& p)
    {
        value = p.value;
    }

    Pointer8B& operator= (const void* ptr)
    {
        value = (unsigned long long)ptr;
        return *this;
    }
    Pointer8B& operator= (const Pointer8B& p)
    {
        value = p.value;
        return *this;
    }

    bool operator== (const void* ptr) {
        bool result = (value == (unsigned long long)ptr);
        return result;
    }
    bool operator== (const Pointer8B& p) {
        bool result = (value == p.value);
        return result;
    }


    operator void* () { return (void*)value; }
    operator char* () { return (char*)value; }
    operator struct INode* () { return (struct INode*)value; }
    operator struct Node* () { return (struct Node*)value; }
    operator unsigned long long() { return value; }

    bool isNull(void) { return (value == 0); }

    void print(void) { printf("%llx\n", value); }

}; // Pointer8B

class btree;
//class LNode;
class Node;
class header {
private:
    // header in persistent memory, 16 bytes
    uint16_t bitmap : 3;
    uint16_t field_type : 3;    //the operation type of lazy field,1:insert or update,0:deleted
    uint16_t moving : 1;        //lazy field is moving
    uint16_t lazy : 1;          // asy update the node
    uint16_t  lock_location : 7; //the location in the slot array,non-persistent
    uint16_t  deleted : 1;
    uint16_t num;                       // 2 bytes
    std::atomic<uint32_t> version_lock;      // 4 bytes
    Node* sibling_ptr;                // 8 bytes

 

    friend class INode;
    friend class Node;
    friend class btree;

public:
    header() {
        version_lock.store(2, std::memory_order_release);
        num = 0;
        clearBit(3);
        clearLazyfield(3);
        moving = 0;
        lazy = 0;
        lock_location = 0;
        deleted = 0;
        sibling_ptr = NULL;

    }

    ~header() { }

    void setBit(int pos) {
        bitmap |= 1UL << pos;
    }
    void resetBit(int pos) {
        bitmap &= ~(1UL << pos);
    }
    void clearBit(int num)
    {
        for (int k = 0; k < num; k++)
        {
            resetBit(k);
        }
    }

    int comparebitmap(int pos)
    {
        int temp;
        int tbitmap = bitmap;
        temp = tbitmap & (1UL << pos);
        if (temp > 0)
        {
            return 1;
        }
        else
        {
            return 0;
        }
    }

    int comparelazyfield(int pos)
    {
        int temp;
        int tlazy = field_type;
        temp = tlazy & (1UL << pos);
        if (temp > 0)
        {
            return 1;
        }
        else
        {
            return 0;
        }
    }

    void clearLazyfield(int num)
    {
        for (int k = 0; k < num; k++)
        {
            field_type &= ~(1UL << k);
        }
    }

    void setLazyfield(int pos) {
        field_type |= 1UL << pos;
    }

    void resetLazyfield(int pos) {
        field_type &= ~(1UL << pos);
    }

    int lazyfield_count() 
    {
        return countBit(bitmap);
    }

    int insert_count()
    {
        int numEntries = 0;
        for (int i = 0; i < lazy_entry; i++) {
            if (comparebitmap(i) && comparelazyfield(i)) {
                numEntries++;
            }
        }
        return numEntries;
    }

    int delete_count()
    {
        int numEntries = 0;
        for (int i = 0; i < lazy_entry; i++) {
            //查看bitmap每个比特是否为0
            if (comparebitmap(i) && !comparelazyfield(i)) {
                numEntries++;
            }
        }
        return numEntries;
    }

    int Ilazyfield_count()
    {
        int numEntries = 0;
        for (int i = 1; i < lazy_entry; i++) {
            if (comparebitmap(i)) {
                numEntries++;
            }
        }
        return numEntries;
    }

    int Iinsert_count()
    {
        int numEntries = 0;
        for (int i = 1; i < lazy_entry; i++) {
            if (comparebitmap(i)) {
                numEntries++;
            }
        }
        return numEntries;
    }

    int Idelete_count()
    {
        int numEntries = 0;
        for (int i = 1; i < lazy_entry; i++) {
            //查看bitmap每个比特是否为0
            if (comparebitmap(i) && !comparelazyfield(i)) {
                numEntries++;
            }
        }
        return numEntries;
    }

    uint32_t getlock() {
        std::atomic_thread_fence(std::memory_order_acquire);
        uint32_t ver = version_lock.load(std::memory_order_acquire);
        return ver;
    }



    uint32_t vlock() {
	std::atomic_thread_fence(std::memory_order_acquire);
        uint32_t ver = version_lock.load(std::memory_order_acquire);
        if (ver < 2) {
            int new_ver = 3;
            if (version_lock.compare_exchange_weak(ver, new_ver)) {
                return new_ver;
            }
            return 0;
        }
        else
        {
            if ((ver & 1) == 0 && version_lock.compare_exchange_weak(ver, ver + 1))
            {
                return ver;
            }
        }
        return 0;
    }


    void vunlock() {
        version_lock.fetch_add(1, std::memory_order_release);
        return;
    }

    uint32_t lockstatus() {
        std::atomic_thread_fence(std::memory_order_acquire);
        uint32_t ver = version_lock.load(std::memory_order_acquire);
        return (ver & 1);
    }
/*
    uint32_t getlock() {
        std::atomic_thread_fence(std::memory_order_acquire);
        uint32_t ver = version_lock.load(std::memory_order_acquire);
        return ver;
    }
*/
};

class Iheader {
private:
    uint64_t num;                       // 4 bytes
    std::atomic<uint64_t> version_lock;  // 4 bytes
    INode* sibling_ptr;                // 8 bytes
    Pointer8B left_ptr;                // 8 bytes
    
    
    friend class INode;
    friend class Node;
    friend class btree;

public:
    Iheader(){
        version_lock.store(2, std::memory_order_release);
        num = 0;
        sibling_ptr = NULL;
        left_ptr = NULL;
    }

    ~Iheader() { }
 
    uint64_t getlock() {
        std::atomic_thread_fence(std::memory_order_acquire);
        uint64_t ver = version_lock.load(std::memory_order_acquire);
        return ver;
    }

    uint64_t vlock() {
        std::atomic_thread_fence(std::memory_order_acquire);
        uint64_t ver = version_lock.load(std::memory_order_acquire);
        if (ver < 2) {
            int new_ver = 3;
            if (version_lock.compare_exchange_weak(ver, new_ver)) {
                return new_ver;
            }
            return 0;
        }
        else
        {
            if ((ver & 1) == 0 && version_lock.compare_exchange_weak(ver, ver + 1))
            {
                return ver;
            }
        }
        return 0;
    }


    void vunlock() {
        version_lock.fetch_add(1, std::memory_order_release);
        return;
    }

    uint64_t lockstatus() {
        std::atomic_thread_fence(std::memory_order_acquire);
        uint64_t ver = version_lock.load(std::memory_order_acquire);
        return (ver & 1);
    }
  
};

class entry {
private:
    entry_key_t key; // 8 bytes
    Pointer8B ptr; // 8 bytes

public:
    entry() {
        key = LONG_MAX;
        ptr = NULL;
    }

    friend class INode;
    friend class Node;
    friend class btree;
};

const int count_in_line = CACHE_LINE_SIZE / sizeof(entry);
const int lazy_count = (CACHE_LINE_SIZE - sizeof(header)) / sizeof(entry);
const int cardinality = ((NodeSIZE - sizeof(header)) / sizeof(entry)) - lazy_count;
const int Inode_cardinality = ((NodeSIZE - sizeof(Iheader)) / sizeof(entry));

class Node{
private:
    header hdr;  // header in persistent memory, 8 bytes
    entry lazy_field[lazy_count]; // slot in a lazy persistent mothd
    entry records[cardinality]; // slots in persistent memory, 16 bytes * n

public:
    friend class btree;

    entry_key_t k(int idx) { return records[idx].key; }
    Pointer8B ch(int idx) { return records[idx].ptr; }

    int linear_scan(entry_key_t bkey, entry_key_t ekey, int len, entry_key_t result[])
    {
        int entry_num;
        //int oldnum;
        int lazynum;
        int count;
        int delnum;
        int insertnum;
    restart:        
        count = 0;
        //lazy field is moving or node is splitting
        if (hdr.lockstatus()) {
            if (hdr.moving)
            {
                goto restart;
            }            
        }
        entry_num = hdr.num;
        lazynum = hdr.lazyfield_count();
        insertnum = lazynum;
        
        //2.1、search lazy field and slot array
        entry sortentry[3];
        int sortnum = 0;
	    entry_key_t max_key = records[entry_num - 1].key;
        entry_key_t min_key = records[0].key;
        for (int fh = 0; fh < 3; fh++)
        {
            if (hdr.comparebitmap(fh))
            {
		        if (min_key > lazy_field[fh].key)
            	{
                	min_key = lazy_field[fh].key;
            	}
            	if (max_key < lazy_field[fh].key)
           	    {
               		max_key = lazy_field[fh].key;
            	}
                if (lazy_field[fh].key > bkey && lazy_field[fh].key < ekey)
                {
                    int sh = sortnum;
                    for (; sh > 0; sh--)
                    {
                        if (lazy_field[fh].key < sortentry[sh - 1].key)
                        {
                            sortentry[sh].key = sortentry[sh - 1].key;
                            sortentry[sh].ptr = sortentry[sh - 1].ptr;
                        }
                        else
                        {
                            break;
                        }
                    }
                    sortentry[sh].key = lazy_field[fh].key;
                    sortentry[sh].ptr = lazy_field[fh].ptr;
                    sortnum++;
                }                
            }
        }

        //2.1.1、ekey > maxkey and bkey > minkey
        if (ekey > max_key && bkey > min_key)
        {
            int lazykeys = 0;
            for (int i = 0; i < entry_num; i++)
            {
                if (count > len) { return count; }
                if (records[i].key > bkey)
                {
                    result[count] = records[i].key;
                    count++;
                    if (lazykeys < sortnum)
                    { 
                        if (sortentry[lazykeys].key> bkey)
                        {
                            if (sortentry[lazykeys].key <= records[i].key)
                            {
				                if(sortentry[lazykeys].key <= records[i].key){lazykeys++;}
				                else{
                                result[count] = result[count - 1];
                                result[count - 1] = sortentry[lazykeys].key;
                                lazykeys++;
                                count++;
				}
                            }
                        }
                        else
                        {
                            lazykeys++;
                        }
                    }                    
                }                
            }
        
        if (hdr.num != entry_num || hdr.moving == 1)
        {
           goto restart;
        }
	    else{
           	return count;  
	    }        
        }

        //2.1.2、ekey > maxkey and bkey < minkey
        if (ekey > max_key && bkey < min_key)
        {
            int totalnum = entry_num + lazynum;
            if (len > totalnum)
            {
                count = totalnum;
                int g = 0;
                for (; g < entry_num; g++)
                {
                    result[g] = records[g].key;
                }
                for (int h = 0; h < lazynum; h++)
                {
                    result[g] = sortentry[h].key;
                    g++;
                }
	    }
	    else{
            int lazykeys = 0;
            for (int i = 0; i < entry_num; i++)
            {
                if (count > len) { return count; }
                result[count] = records[i].key;
                count++;
                if (lazykeys < lazynum)
                {
                    if (sortentry[lazykeys].key <= records[i].key)
                    {
			            if(sortentry[lazykeys].key <= records[i].key){lazykeys++;}
                        else{
                        result[count] = result[count - 1];
                        result[count - 1] = sortentry[lazykeys].key;
                        lazykeys++;
                        count++;
			}
                    }
                }
            }
	    }
        if (hdr.num != entry_num || hdr.moving == 1)
        {
           goto restart;
        }
	    else{
           	return count;
	    }

        }

        //2.1.3、ekey < maxkey and bkey < minkey
        if (ekey < max_key && bkey < min_key)
        {     
            int lazykeys = 0;
            for (int i = 0; i < entry_num; i++)
            {
                if (count > len) { return count; }
                result[count] = records[i].key;
                count++;
                if (records[i].key < ekey)
                {               
                    if (lazykeys < lazynum)
                    {
                        if (sortentry[lazykeys].key < ekey)
                        {
                            if (sortentry[lazykeys].key <= records[i].key)
                            {
				                if(sortentry[lazykeys].key <= records[i].key){lazykeys++;}
                                else{
                                result[count] = result[count - 1];
                                result[count - 1] = sortentry[lazykeys].key;
                                lazykeys++;
                                count++;
				}
                            }
                        }
                        else
                        {
                            lazykeys = lazynum;
                        }
                    }
                }
                else
                {
                    break;
                }
            }
            
            if (hdr.num != entry_num || hdr.moving == 1)
            {
                goto restart;
            }
            else{
                return count;
            }
   
        }
        return count;
    }

    int lazy_compare(entry_key_t key)
    {
        int entrynum = hdr.num;
        if (key > records[entrynum - 1].key)
        {
            return 0;
        }
        else
        {
            int mov_pos = cardinality - (cardinality / 4);
            if (key > records[mov_pos - 1].key)
            {
                return 1;
            }
            else
            {
                return 2;
            }
        }
    }
};

class INode {
private:
    Iheader hdr;  // header in persistent memory, 24 bytes
    entry records[Inode_cardinality]; // slots in persistent memory, 16 bytes * n

public:
    friend class btree;
    friend class Node;
    entry_key_t k(int idx) { return records[idx].key; }
    Pointer8B ch(int idx) { return records[idx].ptr; }
    int lazy_compare(entry_key_t key)
    {        
        int mov_pos = Inode_cardinality - (Inode_cardinality / 4);
        if (key > records[mov_pos - 1].key)
        {
            return 1;
        }
        else
        {
            return 0;
        }
    }
};

#ifdef USE_PMDK
POBJ_LAYOUT_BEGIN(btree);
POBJ_LAYOUT_ROOT(btree, btree);
POBJ_LAYOUT_TOID(btree, INode);
POBJ_LAYOUT_TOID(btree, Node);
POBJ_LAYOUT_END(btree);
PMEMobjpool *pop;
#endif
void *alloc(size_t size){
  TOID(Node) bp;
  POBJ_ZALLOC(pop, &bp.oid, Node, size);
  return (void *)pmemobj_direct(bp.oid);
}

void* Ialloc(size_t size) {
    TOID(INode) Ibp;
    POBJ_ZALLOC(pop, &Ibp.oid, INode, size);
    return (void*)pmemobj_direct(Ibp.oid);
}

bool do_flush(uint64_t ptr)
{
   int remainder = ptr % CACHE_LINE_SIZE;
   bool do_flush = (remainder == 0) ||
   ((((int)(remainder + sizeof(entry)) / CACHE_LINE_SIZE) == 1)
       && ((remainder+sizeof(entry))%CACHE_LINE_SIZE)!=0);
   return do_flush;   
}

class btree{
  private:
    int height;
    Pointer8B root;
    Node* first_leaf;

  public:
    btree();
    ~btree();
    void setNewRoot(Pointer8B);
    void node_split(Node *p, entry_key_t key, void* pptr);
    void Inode_split(INode* p, entry_key_t key, Pointer8B pptr, int lev);
    Node* jumpnode(Node* p, entry_key_t key);
    void addInode(entry_key_t, Pointer8B pptr , uint32_t level);
    void delInode(entry_key_t, uint32_t level);
    void insert(entry_key_t, void*); // Insert
    void remove(entry_key_t);        // Remove
    entry_key_t search(entry_key_t);       // Search
    void scan(entry_key_t,entry_key_t ,long); //Scan
    int level() { return height; }
    void print();
    friend class Node;
};


#ifdef USE_PMDK
int file_exists(const char *filename) {
  struct stat buffer;
  return stat(filename, &buffer);
}

void openPmemobjPool() {
  printf("use pmdk!\n");
  char pathname[100] = "/mnt/pm0/WOPE/pool";
  int sds_write_value = 0;
  pmemobj_ctl_set(NULL, "sds.at_create", &sds_write_value);
  if (file_exists(pathname) != 0) {
    printf("create new one.\n");
    if ((pop = pmemobj_create(pathname, POBJ_LAYOUT_NAME(btree),
                              (uint64_t)200 * 1024 * 1024 * 1024, 0666)) ==
        NULL) {
      perror("failed to create pool.\n");
      return;
    }
  }
  else {
    printf("open existing one.\n");
    if ((pop = pmemobj_open(pathname, POBJ_LAYOUT_NAME(btree))) == NULL) {
      perror("failed to open pool.\n");
      return;
    }
  }

}
#endif
/*
 * class btree
 */
btree::btree(){
  openPmemobjPool();
  root = (Pointer8B)alloc(sizeof(Node));
  first_leaf = root;
  height = 1;
}

btree::~btree() { 
#ifdef USE_PMDK
  pmemobj_close(pop); 
#endif
}

void btree::setNewRoot(Pointer8B new_root) {
  this->root = new_root;
  ++height;
  clflush(root, CACHE_LINE_SIZE);
}

void btree::node_split(Node* p, entry_key_t key, void* pptr)
{
    int countlazy = p->hdr.lazyfield_count();
    int entrynum = p->hdr.num;
    int insernum = countlazy;
    entry_key_t min_lkey;

    int flresult[3] = { 0 };
    min_lkey = key;
    flresult[p->lazy_compare(key)]++;
    for (int i = 0; i < countlazy; i++)
    {
        int m_result;
        m_result = p->lazy_compare(p->lazy_field[i].key);
        flresult[m_result]++;
        if (p->lazy_field[i].key < min_lkey)
        {
            min_lkey = p->lazy_field[i].key;
        }
    }

    //search the location in slot array of lazy field key
    int current_location = 0;
    int bg = 0;
    int ed = entrynum - 1;
    int middl = 0;
    while (bg < ed)
    {
        middl = (bg + ed) / 2;
        if (p->records[middl].key <= min_lkey && p->records[middl+1].key > min_lkey)
        {
            break;
        }
        else
        {
            if (p->records[middl].key > min_lkey)
            {
                ed = middl - 1;
            }
            else
            {
                bg = middl + 1;
            }
        }
    }
    current_location = middl;   
    //new node
    Node* newnode = (Node*)alloc(sizeof(Node));
    newnode->hdr.vlock();

    //move the last cache line entry to new node
    int move_cachenum = 0;
    int cache_num = cardinality / count_in_line;
    if (flresult[0] >= insernum && flresult[0] > 2)
    {
        move_cachenum = cardinality - count_in_line;
    }
    else
    {
        //move the M/4 entry to new node
        if ((flresult[1]+ flresult[0]) >= insernum)
        {
            move_cachenum = cardinality - (count_in_line * (cache_num / 4));
        }
        else
        {
            //move the M/2 entry to new node
            move_cachenum = cardinality - (count_in_line * (cache_num / 2));
        }
    }

    //set moving field and lock_location field
    if (current_location > move_cachenum)
    {
        current_location = move_cachenum - 1;
    }
    p->hdr.lock_location = current_location;
    p->hdr.moving = 1;

    int local_pos = 0;
    int lazy_pos = 0;
    int old_entrynum = move_cachenum;
    int m = move_cachenum;
    for (; m < entrynum; m++)
    {
        newnode->records[local_pos].key = p->records[m].key;
        newnode->records[local_pos].ptr = p->records[m].ptr;
        local_pos++;        
    }
    //insert into new node
    for(int snum=0;snum < 4;snum++)
    {
        entry_key_t ikey;
        Pointer8B iptr;
        if (snum == 0)
        {
            ikey = key;
            iptr = pptr;
        }
	else
        {
            ikey = p->lazy_field[snum-1].key;
            iptr = p->lazy_field[snum-1].ptr;
        }
        //insert into new node
        if (newnode->records[0].key <= ikey)
        {
            int s = local_pos;
            for (; s > 0; s--)
            {
                if (newnode->records[s - 1].key <= ikey)
                {
                    //the key is exist
                    if (newnode->records[s - 1].key == ikey)
                    {
                        //newnode->records[s - 1].ptr = iptr;
			lazy_pos++;
                        break;
                    }
                    //insert to new slot
		    else
                    {
			for(int kh=local_pos;kh > s;kh--)
			{
			    newnode->records[kh] = newnode->records[kh - 1];
			}
                        newnode->records[s].key = ikey;
                        newnode->records[s].ptr = iptr;
                        local_pos++;
                        lazy_pos++;
                        break;
                    }                 
                }
            }
            if (s == 0)
            {
		for (int kh = local_pos; kh > s; kh--)
                {
                   newnode->records[kh] = newnode->records[kh - 1];
                }
                newnode->records[s].key = ikey;
                newnode->records[s].ptr = iptr;
                local_pos++;
                lazy_pos++;
            }
        }
    }
  
    newnode->hdr.sibling_ptr = p->hdr.sibling_ptr;
    p->hdr.sibling_ptr = newnode;
    newnode->hdr.num = local_pos;
    newnode->hdr.lazy = 0;
    delclflushmore(&(newnode->records[0]), &(newnode->records[local_pos - 1]));
    clflush(newnode, CACHE_LINE_SIZE);
    clflush(p, CACHE_LINE_SIZE);
    //insert into old node
    for(int snu=0;snu< 4 && lazy_pos < 4; snu++)
    {
        entry_key_t ikey;
        Pointer8B iptr;
        if (snu == 0)
        {
            ikey = key;
            iptr = pptr;
        }
        else
        {
            ikey = p->lazy_field[snu-1].key;
            iptr = p->lazy_field[snu-1].ptr;
        }
       
        if (newnode->records[0].key > ikey)
        {
            int ff = old_entrynum;
            for (; ff > 0; ff--)
            {
                if (p->records[ff - 1].key <= ikey)
                {
		//the key is exist
                    if (newnode->records[ff - 1].key == ikey)
                    {
                        //newnode->records[s - 1].ptr = iptr;
                        lazy_pos++;
                        break;
                    }
		    else
		    {
                     for (int kh = old_entrynum; kh > ff; kh--)
                        {
                            p->records[kh] = p->records[kh - 1];
                        }
                        p->records[ff].key = ikey;
                        p->records[ff].ptr = iptr;
			if(do_flush((uint64_t)(&p->records[ff])))
                         {
                              clflush(&p->records[ff], CACHE_LINE_SIZE);
                         }
                        old_entrynum++;
                        lazy_pos++;
                        break;
		    }
                }
            }
            if (ff == 0)
            {
                for (int kh = old_entrynum; kh > ff; kh--)
                {
                   p->records[kh] = p->records[kh - 1];
                }
                p->records[ff].key = ikey;
                p->records[ff].ptr = iptr;
		if(do_flush((uint64_t)(&p->records[ff])))
                {
                     clflush(&p->records[ff], CACHE_LINE_SIZE);
                }
                old_entrynum++;
                lazy_pos++;

	    }
	}
    }
    p->hdr.clearBit(lazy_count);
    p->hdr.num = old_entrynum;
    p->hdr.moving = 0;
    clflush(p, CACHE_LINE_SIZE);

    if ( height == 1)
    {
        INode* newroot = (INode*)Ialloc(sizeof(INode));
        newroot->hdr.vlock();
        newroot->records[0].key = newnode->records[0].key;
        newroot->records[0].ptr = newnode;
        newroot->hdr.left_ptr = p;
        newroot->hdr.num = 1;
        clflush(&(newroot->records[0]), CACHE_LINE_SIZE);
        clflush(newroot, CACHE_LINE_SIZE);
        setNewRoot(newroot);
        newroot->hdr.vunlock();
	    p->hdr.vunlock();
	    newnode->hdr.vunlock();
        return;
    }
    else
    {
	    p->hdr.vunlock();
        addInode(newnode->records[0].key, newnode, height - 1);
        newnode->hdr.vunlock();
        return;

    }
}

void btree::Inode_split(INode* p, entry_key_t key, Pointer8B pptr, int lev)
{ 
    //new node
    INode* newnode = (INode*)Ialloc(sizeof(INode));
    newnode->hdr.vlock();

    //move the last cache line entry to new node
    int move_cachenum = 0;
    int cache_num = Inode_cardinality / count_in_line;
    int entry_num = p->hdr.num - 1;
    //move the M/4 entry to new node
    if (p->lazy_compare(key))
    {
        move_cachenum = Inode_cardinality - (count_in_line * (cache_num / 4));
    }
    else
    {
        //move the M/2 entry to new node
        move_cachenum = Inode_cardinality - (count_in_line * (cache_num / 2));
    }

    int local_pos = 0;
    int old_entrynum = move_cachenum;
    int m = move_cachenum;
    newnode->hdr.left_ptr = p->records[m].ptr;
    entry_key_t tem_key = p->records[m].key;
    m++;
    for (; m < p->hdr.num; m++)
    {
        newnode->records[local_pos].key = p->records[m].key;
        newnode->records[local_pos].ptr = p->records[m].ptr;
        local_pos++;
    }
    int ff = old_entrynum;
    //insert into new node
    if (tem_key < key)
    {
        int s = local_pos;
        for (; s > 0; s--)
        {
            if (newnode->records[s - 1].key < key)
            {
                newnode->records[s].key = key;
                newnode->records[s].ptr = pptr;
                local_pos++;  
                break;
            }
            else
            {
                newnode->records[s].key = newnode->records[s - 1].key;
                newnode->records[s].ptr = newnode->records[s - 1].ptr;
                if (s == 1)
                {
                    newnode->records[s - 1].key = key;
                    newnode->records[s - 1].ptr = pptr;
                    local_pos++;
                    break;
                }
            }
        }
        newnode->hdr.num = local_pos;
        newnode->hdr.sibling_ptr = p->hdr.sibling_ptr;
        insclflushmore(&(newnode->records[local_pos - 1].key), &(newnode->records[0].key));
        clflush(newnode, CACHE_LINE_SIZE);
        p->hdr.sibling_ptr = newnode;
        p->hdr.num = old_entrynum;
        clflush(p, CACHE_LINE_SIZE);
    }
    else
    {
        newnode->hdr.num = local_pos;
        newnode->hdr.sibling_ptr = p->hdr.sibling_ptr;
        insclflushmore(&(newnode->records[local_pos - 1].key), &(newnode->records[0].key));
        clflush(newnode, CACHE_LINE_SIZE);
        p->hdr.sibling_ptr = newnode;
        p->hdr.num = old_entrynum;
        clflush(p, CACHE_LINE_SIZE);

        //insert into old node 
        for (; ff > 0; ff--)
        {
            if (p->records[ff - 1].key < key)
            {
                p->records[ff].key = key;
                p->records[ff].ptr = pptr;
                old_entrynum++; 
                break;
            }
            else
            {
                p->records[ff].key = p->records[ff - 1].key;
                p->records[ff].ptr = p->records[ff - 1].ptr;
                if (ff == 1)
                {
                    p->records[ff - 1].key = key;
                    p->records[ff - 1].ptr = pptr;
                    old_entrynum++;
                    break;
                }
            }
        }
        p->hdr.sibling_ptr = newnode;
        p->hdr.num = old_entrynum;
        insclflushmore(&(p->records[old_entrynum - 1]), &(p->records[ff - 1]));
        clflush(p, CACHE_LINE_SIZE);
    }

    //node is root 
    if (lev == 1)
    {
        INode* newroot = (INode*)Ialloc(sizeof(INode));
        newroot->hdr.vlock();
        newroot->hdr.left_ptr = p;
        newroot->records[0].ptr = newnode;
        newroot->records[0].key = tem_key;
        newroot->hdr.num = 1;
        clflush(&(newroot->records[0]), CACHE_LINE_SIZE);
        clflush(newroot, CACHE_LINE_SIZE);
        setNewRoot(newroot);
        newroot->hdr.vunlock();
    }
    else
    {
        addInode(tem_key, newnode, lev - 1);
    }
    p->hdr.vunlock();
    newnode->hdr.vunlock();
    return;
}


void btree::delInode(entry_key_t key, uint32_t lev)
{
    INode* p;
    int i, m, t, b;
    int level;
    int lnum;
    int location;
    entry_key_t r;
restart:
    //1、search internal node
    p = root;
    level = lev;
    for (i = level; i > 1; i--)
    {
        int oldnum = p->hdr.getlock();
        if (p->hdr.lockstatus())
        {
            goto restart;
        }
        t = p->hdr.num - 1;
        b = 0;
        //search the slot array
        while (b + 7 <= t) {
            m = (b + t) >> 1;
            r = key - p->k(m);
            if (r > 0) b = m + 1;
            else if (r < 0) t = m - 1;
            else {
                if (oldnum != p->hdr.getlock())
                {
                    goto restart;
                }
                p = p->ch(m);
                goto inner_done;
            }
        }
        for (; b <= t; b++)
        {
            if (key < p->k(b)) break;
        }
        if (b == 0)
        {
            if (oldnum != p->hdr.getlock())
            {
                goto restart;
            }
            p = p->hdr.left_ptr;
        }
        else
        {
            if (oldnum != p->hdr.getlock())
            {
                goto restart;
            }
            p = p->ch(b - 1);
        }
    inner_done:;
    }

    //2、search node
    
    if (!p->hdr.vlock()) { goto restart; }
    int entry_num = p->hdr.num - 1;   

    if (p->hdr.num > 0)
    {              
        if (p->hdr.num == 1 && lev == 1)
        {
            Pointer8B temp;
            if (key < p->records[0].key)
            {
                temp = p->hdr.left_ptr;
            }
            else
            {
                temp = p->records[0].ptr;
            }
            //change root node
            if (height == 2)
            {
                if (!((Node*)temp)->hdr.vlock())
                {
                    p->hdr.vunlock();
                    goto restart;
                }
                root = temp;
                height = height - 1;
                clflush(root, CACHE_LINE_SIZE);
                p->hdr.vunlock();
                ((Node*)temp)->hdr.vunlock();
                return;
            }
            else
            {
                if (!((INode*)temp)->hdr.vlock())
                {
                    p->hdr.vunlock();
                    goto restart;
                }
                root = temp;
                height = height - 1;
                clflush(root, CACHE_LINE_SIZE);
                p->hdr.vunlock();
                ((INode*)temp)->hdr.vunlock();
                return;
            }           
        }
        else
        {
            if (key < p->records[1].key)
            {
		        if(key < p->records[0].key){
               	   p->hdr.left_ptr = p->records[0].ptr;
		        }
                for (int ms = 1; ms < entry_num; ms++)
                {
                    p->records[ms-1].key = p->records[ms].key;
                    p->records[ms-1].ptr = p->records[ms].ptr;
                }
                p->hdr.num = p->hdr.num - 1;                
                delclflushmore(&(p->records[0].key), &(p->records[p->hdr.num - 1].key));
                p->hdr.vunlock();
                return;
            }
            else
            {
                if (key >= p->records[p->hdr.num - 1].key)
                {
                    p->hdr.num = p->hdr.num - 1;
                    clflush(p, CACHE_LINE_SIZE);
                    p->hdr.vunlock();
                    return;
                }
                else
                {
                    int bg = 0;
                    int ed = p->hdr.num - 1;
                    int middl = 0;
                    while (bg <= ed)
                    {
                        middl = (bg + ed) / 2;
                        if (p->records[middl].key <= key && p->records[middl + 1].key > key)
                        {
                            for (int ms = middl; ms < p->hdr.num; ms++)
                            {
                                p->records[ms].key = p->records[ms + 1].key;
                                p->records[ms].ptr = p->records[ms + 1].ptr;
                            }
                            p->hdr.num = p->hdr.num - 1;
                            delclflushmore(&(p->records[middl].key), &(p->records[p->hdr.num - 1].key));
                            p->hdr.vunlock();
                            return;                            
                        }
                        else
                        {
                            if (p->records[middl].key > key)
                            {
                                ed = middl - 1;
                            }
                            else
                            {
                                bg = middl + 1;
                            }
                        }
                    }
                }
            } 
            
        }               
    }
    else
    {
        //only a ptr
        delInode(key,lev - 1);
        p->hdr.vunlock();
    }   
}

void btree::addInode(entry_key_t key, Pointer8B pptr, uint32_t lev)
{
    INode* p;
    int i, m, t, b;
    int level;
    int lnum;
    int location;
    entry_key_t r;
restart:
    //1、search internal node
    p = root;
    level = lev;
    for (i = level; i > 1; i--)
    {
        int oldnum = p->hdr.getlock();
        if (p->hdr.lockstatus())
        {
            goto restart;
        }     
        t = p->hdr.num - 1;     
        b = 0;
        //search the slot array
        while (b + 7 <= t) {
            m = (b + t) >> 1;
            r = key - p->k(m);
            if (r > 0) b = m + 1;
            else if (r < 0) t = m - 1;
            else {  
                if (oldnum != p->hdr.getlock())
                {
                    goto restart;
                }
                p = p->ch(m);        
                goto inner_done;
            }
        }
        for (; b <= t; b++)
        {
            if (key < p->k(b)) break;
        }
        if (b == 0)
        {
            if (oldnum != p->hdr.getlock())
            {
                goto restart;
            }
            p = p->hdr.left_ptr;
        }
        else
        {
            if (oldnum != p->hdr.getlock())
            {
                goto restart;
            }
            p = p->ch(b - 1);
        }                    
    inner_done:;
    }
    
    //2、search node
    if (!p->hdr.vlock()) { goto restart; } 
    else
    {
        //2.3、lazy field is full,moving to slot array
        // 2.3.1、slot array is full
        if (p->hdr.num >= Inode_cardinality)
        {
            //node is split
            Inode_split(p, key, pptr, lev);
            return;
        }
        // 2.3.2、slot array is not full
        else
        {
            //insert the key to node
            int hk = p->hdr.num;    
            for (; hk > 0; hk--)
            {
                if (p->records[hk - 1].key < key)
                {                    
                    p->records[hk].key = key;
                    p->records[hk].ptr = pptr;
                    p->hdr.num = p->hdr.num + 1;
                    break;
                }
                else
                {
                    p->records[hk].key = p->records[hk - 1].key;
                    p->records[hk].ptr = p->records[hk - 1].ptr;                    
                }
            }
            if (hk == 0)
            {
                p->records[0].key = key;
                p->records[0].ptr = pptr;
                p->hdr.num = p->hdr.num + 1;
                insclflushmore(&(p->records[p->hdr.num - 1]), &(p->records[hk]));
                p->hdr.vunlock();
                return;
            }     
            //flush slot array
            insclflushmore(&(p->records[p->hdr.num - 1]), &(p->records[hk]));
            
            //flush metadata
            clflush(p, CACHE_LINE_SIZE);
            p->hdr.vunlock();
            return;
        }
    }
}

void btree::remove(entry_key_t key) {
    INode* p;
    Node* lp;
    int i, m, t, b;
    int level;
    int lnum;
    int location;
    entry_key_t r;
restart:
    //1、search internal node
    p = root;
    level = height;
    for (i = level; i > 1; i--)
    {
        int oldnum = p->hdr.getlock();
        if (p->hdr.lockstatus())
        {
            goto restart;
        }
        t = p->hdr.num - 1;
        b = 0;
        //search the slot array
        while (b + 7 <= t) {
            m = (b + t) >> 1;
            r = key - p->k(m);
            if (r > 0) b = m + 1;
            else if (r < 0) t = m - 1;
            else {
                if (oldnum != p->hdr.getlock())
                {
                    goto restart;
                }
                p = p->ch(m);
                goto inner_done;
            }
        }
        for (; b <= t; b++)
        {
            if (key < p->k(b)) break;
        }
        if (b == 0)
        {
            if (oldnum != p->hdr.getlock())
            {
                goto restart;
            }
            p = p->hdr.left_ptr;
        }
        else
        {
            if (oldnum != p->hdr.getlock())
            {
                goto restart;
            }
            p = p->ch(b - 1);
        }
    inner_done:;
    }


    //2、search leaf node
    lp = (Node*)p;   
    if (!lp->hdr.vlock()) { goto restart; }
    bool delflag=false;
    int entry_num = lp->hdr.num;
    int lazynum = lp->hdr.lazyfield_count();
   
    // if the key is exists in the lazy field
    for (int s = 0; s < lazy_count; s++)
    {
        if (lazynum > 0) {
            if (lp->hdr.comparebitmap(s))
            {
                if (key == lp->lazy_field[s].key) {
                    lp->hdr.resetBit(s);
                    lazynum--;
		            delflag=true;
                    break;
                }
            }
        }
        else {
            break;
        }
    }

    //2.3、look up key from slot array
    int bg = 0;
    int ed = entry_num - 1;
    int middl = 0;
    while (bg <= ed)
    {
        middl = (bg + ed) / 2;
        if (lp->records[middl].key == key)
        {
            if (lp->hdr.num == 1 && lazynum == 0)
            {
                //node is NULL
                lp->hdr.num = 0;
                lp->hdr.deleted = 1;

                //node is not lazy node
                if (height > 1)
                {
                    delInode(key, height - 1);
                }

                //next node is del node, del the next node
                if (lp->hdr.sibling_ptr != nullptr)
                {
                    if (lp->hdr.sibling_ptr->hdr.deleted)
                    {
                        if (lp->hdr.sibling_ptr->hdr.vlock())
                        {
                            if (first_leaf == lp)
                            {
                                first_leaf = lp->hdr.sibling_ptr;
                                clflush(first_leaf, CACHE_LINE_SIZE);
                                first_leaf->hdr.vunlock();
                                return;
                            }
                            else
                            {
                                lp->hdr.sibling_ptr = lp->hdr.sibling_ptr->hdr.sibling_ptr;
                                clflush(lp, CACHE_LINE_SIZE);
                                lp->hdr.vunlock();
                                return;
                            }
                        }
                    }
                }
                clflush(lp, CACHE_LINE_SIZE);
                lp->hdr.vunlock();
                return;
            }

            lp->hdr.lock_location = middl - 1;
            lp->hdr.moving = 1;
            for (int fk = middl + 1; fk < entry_num; fk++)
            {
                lp->records[fk - 1] = lp->records[fk];
		if(do_flush((uint64_t)(&lp->records[fk-1])))
                {
                  clflush(&lp->records[fk], CACHE_LINE_SIZE);
                }
            }
            lp->hdr.num = lp->hdr.num - 1;
            lp->hdr.moving = 0;
            if (lp->hdr.num == 0 && lazynum > 0)
            {
                clflush(lp, CACHE_LINE_SIZE);
                lp->hdr.vunlock();
                return;
            }
            else
            {
                //flush slot array
                //delclflushmore(&(lp->records[middl]), &(lp->records[lp->hdr.num - 1]));
                //flush metadata
                clflush(lp, CACHE_LINE_SIZE);
                lp->hdr.vunlock();
                return;
            }
        }
        else
        {
            if (lp->records[middl].key < key)
            {
                bg = middl + 1;
            }
            else
            {
                ed = middl - 1;
            }
        }
    }    
    if(delflag)
    {
	clflush(lp, CACHE_LINE_SIZE);
    }
    lp->hdr.vunlock();
    return;    
}

entry_key_t btree::search(entry_key_t key)
{
    INode* p;
    Node* lp;
    int i, m, t, b;
    int level;
    int lnum;
    int location;
    entry_key_t r;
restart:
    //1、search internal node
    p = root;
    level = height;
    for (i = level; i > 1; i--)
    {
        int oldnum = p->hdr.getlock();
        if (p->hdr.lockstatus())
        {
            goto restart;
        }
        t = p->hdr.num - 1;
        b = 0;
        //search the slot array
        while (b + 7 <= t) {
            m = (b + t) >> 1;
            r = key - p->k(m);
            if (r > 0) b = m + 1;
            else if (r < 0) t = m - 1;
            else {
                if (oldnum != p->hdr.getlock())
                {
                    goto restart;
                }
                p = p->ch(m);
                goto inner_done;
            }
        }
        for (; b <= t; b++)
        {
            if (key < p->k(b)) break;
        }
        if (b == 0)
        {
            if (oldnum != p->hdr.getlock())
            {
                goto restart;
            }
            p = p->hdr.left_ptr;
        }
        else
        {
            if (oldnum != p->hdr.getlock())
            {
                goto restart;
            }
            p = p->ch(b - 1);
        }
    inner_done:;
    }

    //2、search leaf node
    //jump to correct node
    lp = (Node*)p;
    //p = jumpnode(lp,key);
    int entry_num;
    int lazynum = lp->hdr.lazyfield_count();
    bool mv_flag = false;
    entry_key_t pptr = NULL;
    entry_num=lp->hdr.num;
    if (lp->hdr.lockstatus()) {
        if (lp->hdr.moving)
        {
            entry_num = lp->hdr.lock_location;
            mv_flag = true;
        }   
    }
    int old_num = entry_num;
    //2.1、search lazy field
    int bg = 0;
    int ed = entry_num - 1;
    int middl = 0;
    if (!mv_flag)
    {
	if(lazynum > 0)
	{
        int s = 0;
	    int fnum=0;
        // if the key is exists in the lazy field
        for (;fnum < lazynum && s < lazy_count; s++)
        {
            if (lp->hdr.comparebitmap(s))
            {
		fnum++;
                if (key == lp->lazy_field[s].key) {
                    pptr = lp->lazy_field[s].key;
		    goto search_done;
                }
            }           
        }
	}
	   
            //find the location in slot array
            while (bg <= ed)
            {
                middl = (bg + ed) / 2;
                if (lp->records[middl].key == key)
                {
                    pptr = lp->records[middl].key;
                    break;
                }
                else
                {
                    if (lp->records[middl].key < key)
                    {
                        bg = middl+1;
                    }
                    else
                    {
                        ed = middl-1;
                    }
                }
            }
    }     
    else
    {
        //find the location in slot array
        while (bg <= ed)
        {
            middl = (bg + ed) / 2;
            if (lp->records[middl].key == key)
            {
                pptr = lp->records[middl].key;
                break;
            }
            else
            {
                if (lp->records[middl].key < key)
                {
                    bg = middl+1;
                }
                else
                {
                    ed = middl-1;
                }
            }
        }
    }
    //printf("the bg key is %lld,%lld\n",lp->hdr.num,lp->records[bg].key);
search_done:;
    
    if (mv_flag)
    {
        if (middl > ed)
        {
            goto restart;
        }
    }
    else
    {
        if (lp->hdr.moving || old_num < lp->hdr.num)
        {
            goto restart;
        }
    }
    return pptr;
}

void btree::scan(entry_key_t skey, entry_key_t ekey, long len)
{
    INode* p;
    Node* lp;
    INode* temp;
    INode* sibling_node;
    int i, m, t, b;
    int level;
    int lnum;
    int location;
    entry_key_t r;
restart:
    //1、search internal node
    p = root;
    level = height;
    for (i = level; i > 1; i--)
    {
        int oldnum = p->hdr.getlock();
        if (p->hdr.lockstatus())
        {
            goto restart;
        }
        t = p->hdr.num - 1;
        b = 0;
        //search the slot array
        while (b + 7 <= t) {
            m = (b + t) >> 1;
            r = skey - p->k(m);
            if (r > 0) b = m + 1;
            else if (r < 0) t = m - 1;
            else {
                if (oldnum != p->hdr.getlock())
                {
                    goto restart;
                }
                p = p->ch(m);
                goto inner_done;
            }
        }
        for (; b <= t; b++)
        {
            if (skey < p->k(b)) break;
        }
        if (b == 0)
        {
            if (oldnum != p->hdr.getlock())
            {
                goto restart;
            }
            p = p->hdr.left_ptr;
        }
        else
        {
            if (oldnum != p->hdr.getlock())
            {
                goto restart;
            }
            p = p->ch(b - 1);
        }
    inner_done:;
    }

    //2、search leaf node
    lp = (Node*)p;
    std::vector<entry_key_t> results;
    int length = len;
    while (true)
    {
        entry_key_t m_key = lp->records[0].key;
        for (int jk = 0; jk < lazy_count; jk++)
        {
            if (lp->hdr.comparebitmap(jk))
            {
                if (m_key > lp->lazy_field[jk].key)
                {
                    m_key = lp->lazy_field[jk].key;
                }
            }           
        }
        if (m_key > ekey || length <= 0) { break; }
        entry_key_t lrecord[cardinality + lazy_count];
        int key_count = 0;
        key_count = lp->linear_scan(skey, ekey, length, lrecord);
	
        for (int f = 0; f < key_count && length > 0; f++)
        {
            results.push_back(lrecord[f]);
        }
	
	length=length-key_count;
	
	if(lp->hdr.sibling_ptr!=NULL)
	{
        lp = lp->hdr.sibling_ptr;
    }
    }
    return;
}

void btree::insert(entry_key_t key, void* pptr)
{
    INode* p;
    Node* lp;
    int i, m, t, b;
    int level;
    int lnum;
    int location;
    entry_key_t r;
restart:
    //1、search internal node
    p = root;
    level = height;
    for (i = level; i > 1; i--)
    {
        int oldnum = p->hdr.getlock();
        if (p->hdr.lockstatus())
        {
            goto restart;
        }
        t = p->hdr.num - 1;
        b = 0;
        //search the slot array
        while (b + 7 <= t) {
            m = (b + t) >> 1;
            r = key - p->k(m);
            if (r > 0) b = m + 1;
            else if (r < 0) t = m - 1;
            else {
                if (oldnum != p->hdr.getlock())
                {
                    goto restart;
                }
                p = p->ch(m);
                goto inner_done;
            }
        }
        for (; b <= t; b++)
        {
            if (key < p->k(b)) break;
        }
        if (b == 0)
        {
            if (oldnum != p->hdr.getlock())
            {
                goto restart;
            }
            p = p->hdr.left_ptr;
        }
        else
        {
            if (oldnum != p->hdr.getlock())
            {
                goto restart;
            }
            p = p->ch(b - 1);
        }
    inner_done:;
    }
    
    //2、search leaf node
    //jump to correct node
    lp = (Node*)p;
    if (!lp->hdr.vlock()) { goto restart; }
    int entry_num = lp->hdr.num;
    int lazynum = lp->hdr.lazyfield_count();
    //if the key is exists in the lazy field
    for (int s = 0; s < 3; s++)
    {
        if (lp->hdr.comparebitmap(s))
        {
           if(key == lp->lazy_field[s].key) {
		
                lp->lazy_field[s].ptr = pptr;
                clflush(lp, CACHE_LINE_SIZE);
                lp->hdr.vunlock();
                return;
            }
        }
    }
    //lazy field is not full
    if (lazynum < lazy_count)
    {
        for (int ss = 0; ss < 3; ss++)
        {
            if (lp->hdr.comparebitmap(ss)==0)
            {
                lp->lazy_field[ss].key = key;
                lp->lazy_field[ss].ptr = pptr;
                lp->hdr.setBit(ss);
                clflush(lp, CACHE_LINE_SIZE);
                lp->hdr.vunlock();
                return;
            }
        }
    }
    else
    {
        int insertnum = lazynum;
        int total_num = insertnum + entry_num;
        // 2.3.1、slot array is full
        if (total_num >= cardinality)
        {
            //node is split
            node_split(lp, key, pptr);
            return;
        }
        else
        {
            //slot array is not full
            entry_key_t min_key;
            min_key = key;
            for (int kt = 0; kt < 3; kt++)
            {
                if (min_key > lp->lazy_field[kt].key)
                {
                    min_key = lp->lazy_field[kt].key;
                }
            }

            //find the location in slot array
            int current_location = 0;
            int bg = 0;
            int ed = entry_num - 1;
            int middl = 0;
            while (bg < ed)
            {
                middl = (bg + ed) / 2;
                if (lp->records[middl].key <= min_key && lp->records[middl + 1].key > min_key)
                {
                    break;
                }
                else
                {
                    if (lp->records[middl].key < min_key)
                    {
                        bg = middl + 1;
                    }
                    else
                    {
                        ed = middl-1;
                    }
                }
            }
            current_location = bg;
            
            //moving lazy field to slot array
            lp->hdr.lock_location = current_location;
            lp->hdr.moving = 1;

            int g = 3;

            int hk = lp->hdr.num;
            entry sortentry[4];
            sortentry[0].key = key;
            sortentry[0].ptr = pptr;
            
            for (int kt = 0; kt < 3; kt++)
            {
                sortentry[kt + 1].key = lp->lazy_field[kt].key;
                sortentry[kt + 1].ptr = lp->lazy_field[kt].ptr;
            }
            //sort lazy entry
            for (int kk = 0; kk < 4; kk++)
            {
                entry_key_t kkey = sortentry[kk].key;
                char* kptr = sortentry[kk].ptr;
                int pos = kk;
                int ks = kk + 1;
                for (; ks < 4; ks++)
                {
                    if (kkey > sortentry[ks].key)
                    {
                        kkey = sortentry[ks].key;
                        kptr = sortentry[ks].ptr;
                        pos = ks;
                    }
                }
                if (pos != kk)
                {
                    sortentry[pos].key = sortentry[kk].key;
                    sortentry[pos].ptr = sortentry[kk].ptr;
                    sortentry[kk].key = kkey;
                    sortentry[kk].ptr = kptr;
                }
            }
            //find repeat entry
            int srp = g;
            int gp = g;
            for (int rp = entry_num - 1; rp >= bg; rp--)
            {
                if (lp->records[rp].key <= sortentry[srp].key)
                {
                    if (lp->records[rp].key == sortentry[srp].key)
                    {                        
                        gp--;
                    }
                    srp--;
                }                   
            }

            //move from lazy to slot
	   
            for (; g >= 0 && hk > 0; )
            {		    
		        	 
		        if (lp->records[hk - 1].key > sortentry[g].key)
                {
                        lp->records[hk+gp].key = lp->records[hk - 1].key;
                        lp->records[hk+gp].ptr = lp->records[hk - 1].ptr;
                        if(do_flush((uint64_t)(&lp->records[hk+gp])))
                        {
                              clflush(&lp->records[hk+gp], CACHE_LINE_SIZE);
                        }
			            hk--;
		        }
		        else
                {		  
                    if (lp->records[hk - 1].key == sortentry[g].key)
                    {
                        lp->records[hk - 1].ptr = sortentry[g].ptr;
                        g--;
                        clflush(&lp->records[hk - 1], CACHE_LINE_SIZE);
                        continue;
                    }
                    else
                    {
                        lp->records[hk + gp].key = sortentry[g].key;
                        lp->records[hk + gp].ptr = sortentry[g].ptr;
                        entry_num++;
                        if (do_flush((uint64_t)(&lp->records[hk + gp])))
                        {
                            clflush(&lp->records[hk + gp], CACHE_LINE_SIZE);
                        }
                        g--;
                        gp--;
                    }                   
                }
            }
	    
            while (g >= 0)
            {		    
		        lp->records[gp].key = sortentry[g].key;
                lp->records[gp].ptr = sortentry[g].ptr;
		        entry_num++;
                g--;
                gp--;
            }
                
            if(hk==0) {clflush(&lp->records[0], CACHE_LINE_SIZE);}
            //flush slot arry
            lp->hdr.num = entry_num;
            lp->hdr.clearBit(lazy_count);

            //flush metadata
            //if fail,look up moving field when recovery,
            //if true,recovery the correct data by the lazy field
            lp->hdr.moving = 0;
            clflush(lp, CACHE_LINE_SIZE);	   
            lp->hdr.vunlock();
            return;
        }
    }
}


#define CUSTOM_GRANULARITY ((1 << 20) * 10)
void btree::print()
{
   Node* lp;
   lp=first_leaf;
   int numb=0;
   int allocat=0;
   while(lp!=NULL)
   {
	 int count=lp->hdr.lazyfield_count();
	 numb = numb + lp->hdr.num + count;
	 allocat++;
	 lp = lp->hdr.sibling_ptr;
   }
   printf("total num is %lld\n",numb);
}
