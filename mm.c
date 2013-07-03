/*
 * Use fixed-width bins
 * see http://gee.cs.oswego.edu/dl/html/malloc.html
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "5120379037",
    /* First member's full name */
    "jin tian",
    /* First member's email address */
    "myisjt@gmail.com",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""
};


/* Basic constants and macros */
#define WSIZE       4       /* Word and header/footer size (bytes) */ 
#define DSIZE       8       /* Doubleword size (bytes) */
#define CHUNKSIZE  (1<<12)  /* Extend heap by this amount (bytes) */  

#define MAX(x, y) ((x) > (y)? (x) : (y))  

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc)  ((size) | (alloc)) 

/* Read and write a word at address p */
#define GET(p)       (*(unsigned int *)(p))            
#define PUT(p, val)  (*(unsigned int *)(p) = (val))    

/* Read and write a pointer at address p */
#define GET_PTR(p) ((unsigned int *)(GET(p)))
#define PUT_PTR(p, ptr) (*(unsigned int *)(p) = (unsigned int *)(ptr))

/* Given block ptr bp, compute address of next and previous free blocks in its bin */
#define PREV_FBP(p) GET_PTR(((char*)(p))+WSIZE)
#define NEXT_FBP(p) GET_PTR((p))

/* Read the size and allocated fields from address p */
#define GET_SIZE(p)  (GET(p) & ~0x7)                   
#define GET_ALLOC(p) (GET(p) & 0x1)                    

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp)       ((char *)(bp) - WSIZE)                      //line:vm:mm:hdrp
#define FTRP(bp)       ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE) //line:vm:mm:ftrp

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp)  ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE))) //line:vm:mm:nextblkp
#define PREV_BLKP(bp)  ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE))) //line:vm:mm:prevblkp


/*
 * Exact:
 *	0	1	2	....	61
 *	16	24	32	....	504
 * Step1: step=64
 *	62	63	64	....	85
 *	512	576	640	....	1984
 * Step2: step=2048
 *	86		87		88		....	100
 *	2048	4096	6144	....	30720
 * Double
 *	101		102		103		104		105		
 *	32768	65535	131072	262144	524288
 *
 */
/* Constants for bins */

#define BINSIZE		126			/* Size of fixed-width bins */
#define EXACT_BIN	62			/* Number of exact one size bins */
#define STEP_BIN_1	24
#define BIN_STEP_1	64
#define STEP_BIN_2	15		
#define BIN_STEP_2	2048
#define MAX_EXACT	(1+EXACT_BIN)*DSIZE	 /* 504 */					
#define MAX_STEP_1	(MAX_EXACT+BIN_STEP_1*STEP_BIN_1) /* 2040 */
#define MAX_STEP_2	(MAX_STEP_1+BIN_STEP_2*STEP_BIN_2) /* 32760 */

/* Global variables */
static char *heap_listp = 0;  /* Pointer to first block */  
static char *bin_listp = 0; /* Pointer to bin_list */

/* Function prototypes for internal helper routines */
static void *extend_heap(size_t words);
static void* place(void *bp, size_t asize);
static void *find_fit(size_t asize);
static void *coalesce(void *bp);
static void printblock(void *bp); 
static void checkheap(int verbose);
static int  checkblock(void *bp);
static void put_bin(void *bp);
static void delete_bin(void *bp);
static unsigned get_index(size_t size);
static void dump_bin();


#define DEBUGx
#define BIN
#define ASSERTSx
#define NEW_REALLOCx

/* 
 * mm_init - Initialize the memory manager 
 */
int mm_init(void) 
{
	/* Create the initial empty heap */
	if ((heap_listp = mem_sbrk((BINSIZE+4)*WSIZE)) == (void *)-1) 
		return -1;
	int i;
	bin_listp = heap_listp;
	for (i=0; i < BINSIZE; ++i)
		PUT_PTR(heap_listp + i*WSIZE, NULL);			/* initialize to null */
	PUT(heap_listp + ((BINSIZE)*WSIZE), 0);                 /* Alignment padding */
	PUT(heap_listp + ((BINSIZE+1)*WSIZE), PACK(DSIZE, 1)); /* Prologue header */ 
	PUT(heap_listp + ((BINSIZE+2)*WSIZE), PACK(DSIZE, 1)); /* Prologue footer */ 
	PUT(heap_listp + ((BINSIZE+3)*WSIZE), PACK(0, 1));     /* Epilogue header */
	heap_listp += ((BINSIZE+2)*WSIZE);                       
	/* Extend the empty heap with a free block of CHUNKSIZE bytes */
	if (extend_heap(CHUNKSIZE/WSIZE) == NULL) 
		return -1;
	return 0;
}

/* 
 * mm_malloc - Allocate a block with at least size bytes of payload 
 */
void *mm_malloc(size_t size) 
{
#ifdef DEBUG
	printf("\n--------------------------\nmalloc: %d\n", size);
#endif
	size_t asize;      /* Adjusted block size */
	size_t extendsize; /* Amount to extend heap if no fit */
	char *bp;      

	if (heap_listp == 0){
		mm_init();
	}
	/* Ignore spurious requests */
	if (size == 0)
		return NULL;

	/* Adjust block size to include overhead and alignment reqs. */
	if (size <= DSIZE)                                       
		asize = 2*DSIZE;                                       
	else
		asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE); 

	/* Search the free list for a fit */
	if ((bp = find_fit(asize)) != NULL) {  
		bp = place(bp, asize);                  
#ifdef DEBUG
		checkheap(1);
		dump_bin();
#endif
		return bp;
	}

	/* No fit found. Get more memory and place the block */
	extendsize = MAX(asize,CHUNKSIZE);                
	if ((bp = extend_heap(extendsize/WSIZE)) == NULL)  
		return NULL;                                 
	bp = place(bp, asize);                     
#ifdef DEBUG
		printf("entend for memory \n");
		checkheap(1);
		dump_bin();
#endif
	return bp;
} 

/* 
 * mm_free - Free a block 
 */
void mm_free(void *bp)
{
	if(bp == 0) 
		return;

	size_t size = GET_SIZE(HDRP(bp));
#ifdef DEBUG
	printf("Free %d\n", size);
#endif
	if (heap_listp == 0){
		mm_init();
	}

	PUT(HDRP(bp), PACK(size, 0));
	PUT(FTRP(bp), PACK(size, 0));
#ifdef DEBUG
	checkheap(1);
#endif
	coalesce(bp);

}

/*
 * coalesce - Boundary tag coalescing. Return ptr to coalesced block
 */
static void *coalesce(void *bp) 
{
	size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
	size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
	size_t size = GET_SIZE(HDRP(bp));

	if (prev_alloc && next_alloc) {            /* Case 1 */
	}

	else if (prev_alloc && !next_alloc) {      /* Case 2 */
		size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
		delete_bin(NEXT_BLKP(bp));
		PUT(HDRP(bp), PACK(size, 0));
		PUT(FTRP(bp), PACK(size,0));
	}

	else if (!prev_alloc && next_alloc) {      /* Case 3 */
		size += GET_SIZE(HDRP(PREV_BLKP(bp)));
		delete_bin(PREV_BLKP(bp));
		PUT(FTRP(bp), PACK(size, 0));
		PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
		bp = PREV_BLKP(bp);
	}

	else {                                     /* Case 4 */
		size += GET_SIZE(HDRP(PREV_BLKP(bp))) + 
			GET_SIZE(FTRP(NEXT_BLKP(bp)));
		delete_bin(PREV_BLKP(bp));
		delete_bin(NEXT_BLKP(bp));
		PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
		PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
		bp = PREV_BLKP(bp);
	}
	put_bin(bp);
	return bp;
}

/*
 * put_bin - Put a free block into the bins
 */
static void put_bin(void *bp)
{
#ifdef BIN
	unsigned index;
	size_t size;
	size = GET_SIZE(HDRP(bp));
	index = get_index(size);
	char *dest_bin = bin_listp + WSIZE * index;
#ifdef ASSERTS
	assert(dest_bin < heap_listp);
#endif
	char *old_bp = GET_PTR(dest_bin);
	PUT_PTR(bp, old_bp);
#ifdef ASSERTS
	assert(NEXT_FBP(bp)==old_bp);
#endif
	if (old_bp != NULL) {
		PUT_PTR(old_bp+WSIZE, bp);
#ifdef ASSERTS
		assert(PREV_FBP(old_bp) == bp);
#endif
	}
	PUT_PTR(dest_bin, bp);
	PUT_PTR(bp+WSIZE, dest_bin);
#ifdef ASSERTS
	assert(GET_PTR(dest_bin)==bp);
	assert(PREV_FBP(bp)==dest_bin);
	printf("In put_bin, index:%d\n", index);
	assert(bp==GET_PTR(dest_bin));
	assert(PREV_FBP(GET_PTR(dest_bin))==dest_bin);
	assert(checkblock(bp));
	if (GET_PTR(bp)!=NULL){
		//printblock(GET_PTR(bp));
		assert(checkblock(GET_PTR(bp)));
	}

#endif



#endif
}


static void delete_bin(void *bp)
{
#ifdef BIN
	char * prev = PREV_FBP(bp);
#ifdef ASSERTS
	assert(prev !=NULL);
#endif
	char * succ = NEXT_FBP(bp);
	PUT_PTR(prev, succ);
	if (succ != NULL)
		PUT_PTR(succ+WSIZE, prev);
#endif
}

/* 
 * get_index - get the index of bins in which can the free block put
 */
static unsigned get_index(size_t size)
{
	if (size <= MAX_EXACT){
		return size/DSIZE - 2;

	}
	else if (size <= MAX_STEP_1){
		return (size-MAX_EXACT-DSIZE)/BIN_STEP_1 + EXACT_BIN;
	}
	else if (size <= MAX_STEP_2){
		return (size-MAX_STEP_1-DSIZE)/BIN_STEP_2 + EXACT_BIN+STEP_BIN_1;
	}
	else {
		unsigned r =0;
		while (size >>= 1) ++r;
		return (r-14+EXACT_BIN+STEP_BIN_1+STEP_BIN_2);
	}
}

/*
 * mm_realloc - Naive implementation of realloc
 */
void *mm_realloc(void *ptr, size_t size)
{
	size_t oldsize;
	void *newptr;

	/* If size == 0 then this is just free, and we return NULL. */
	if(size == 0) {
		mm_free(ptr);
		return 0;
	}

	/* If oldptr is NULL, then this is just malloc. */
	if(ptr == NULL) {
		return mm_malloc(size);
	}

#ifndef NEW_REALLOC
	newptr = mm_malloc(size);

	/* If realloc() fails the original block is left untouched  */
	if(!newptr) {
		return 0;
	}

	/* Copy the old data. */
	oldsize = GET_SIZE(HDRP(ptr));
	if(size < oldsize) oldsize = size;
	memcpy(newptr, ptr, oldsize);

	/* Free the old block. */
	mm_free(ptr);

	return newptr;
#else
	
#endif
}

/* 
 * checkheap - We don't check anything right now. 
 */
void mm_checkheap(int verbose)  
{ 
}


/* 
 * The remaining routines are internal helper routines 
 */

/* 
 * extend_heap - Extend heap with free block and return its block pointer
 */
static void *extend_heap(size_t words) 
{
	char *bp;
	size_t size;

	/* Allocate an even number of words to maintain alignment */
	size = (words % 2) ? (words+1) * WSIZE : words * WSIZE; 
	if ((long)(bp = mem_sbrk(size)) == -1)  
		return NULL;                                        

	/* Initialize free block header/footer and the epilogue header */
	PUT(HDRP(bp), PACK(size, 0));         /* Free block header */  
	PUT(FTRP(bp), PACK(size, 0));         /* Free block footer */ 
	PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* New epilogue header */ 

	/* Coalesce if the previous block was free */
	return coalesce(bp);                                         

}

/* 
 * place - Place block of asize bytes at start of free block bp 
 *         and split if remainder would be at least minimum block size
 */
static void* place(void *bp, size_t asize)
{
	size_t csize = GET_SIZE(HDRP(bp));   
	delete_bin(bp);
	if ((csize - asize) >= (2*DSIZE)) { 
		char *old_bp = bp;
		bp = bp + csize-asize;
		PUT(HDRP(bp), PACK(asize, 1));
		PUT(FTRP(bp), PACK(asize, 1));
#ifdef ASSERTS
		assert(FTRP(bp)==FTRP(old_bp));
#endif
		PUT(HDRP(old_bp), PACK(csize-asize, 0));
		PUT(FTRP(old_bp), PACK(csize-asize, 0));
#ifdef ASSERTS
		assert(NEXT_BLKP(old_bp)==bp);
		assert(PREV_BLKP(bp)==old_bp);
		assert(FTRP(old_bp)+WSIZE==HDRP(bp));
#endif
		put_bin(old_bp);
#ifdef ASSERTS
		int index = get_index(csize-asize);
		char* dest_bin=bin_listp+WSIZE*index;
		assert((char*)PREV_FBP(old_bp)==(char *)dest_bin);
		assert(GET_PTR(dest_bin)==old_bp);
		printf("IN place:%d \n",GET_SIZE(HDRP(old_bp)));
#endif
	}
	else { 
		PUT(HDRP(bp), PACK(csize, 1));
		PUT(FTRP(bp), PACK(csize, 1));
	}
	return bp;
}
/* $end mmplace */

/* 
 * find_fit - Find a fit for a block with asize bytes 
 */
static void *find_fit(size_t asize)
{
#ifndef BIN
	/* First fit search */
	void *bp;

	for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
		if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) {
			return bp;
		}
	}
	return NULL; /* No fit */

#else
	int index;
	void *bp;
	for (index = get_index(asize);index < BINSIZE; ++index)
	{
		bp = GET_PTR(bin_listp + index * WSIZE);
		while (bp != NULL){
			if (GET_SIZE(HDRP(bp)) >=asize)
			{
#ifdef ASSERTS
				printf("In find_fit, bp:%x\n",bp);
				assert(PREV_FBP(bp)!=NULL);
#endif
				return bp;
			}
			bp = GET_PTR(bp);
		}
	}
	return NULL;
#endif
}

static void printblock(void *bp) 
{
	size_t hsize, halloc, fsize, falloc;

	checkheap(0);
	hsize = GET_SIZE(HDRP(bp));
	halloc = GET_ALLOC(HDRP(bp));  
	fsize = GET_SIZE(FTRP(bp));
	falloc = GET_ALLOC(FTRP(bp));  

	if (hsize == 0) {
		printf("%p: EOL\n", bp);
		return;
	}

  printf("%p: header: [%p:%c] footer: [%p:%c]\n", bp, 
		hsize, (halloc ? 'a' : 'f'), 
		fsize, (falloc ? 'a' : 'f')); 
}

static int checkblock(void *bp) 
{
	int error = 0;
	if ((size_t)bp % 8)
	{
		error = 1;
		printf("Error: %p is not doubleword aligned\n", bp);
	}
	if (GET(HDRP(bp)) != GET(FTRP(bp)))
	{
		error = 1;
		printf("Error: header does not match footer\n");
	}
	return !error;
}

/* 
 * checkheap - Minimal check of the heap for consistency 
 */
void checkheap(int verbose) 
{
	char *bp = heap_listp;

	if (verbose)
		printf("Heap (%p):\n", heap_listp);

	if ((GET_SIZE(HDRP(heap_listp)) != DSIZE) || !GET_ALLOC(HDRP(heap_listp)))
		printf("Bad prologue header\n");
	checkblock(heap_listp);

	for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
		if (verbose) 
			printblock(bp);
		checkblock(bp);
	}

	if (verbose)
		printblock(bp);
	if ((GET_SIZE(HDRP(bp)) != 0) || !(GET_ALLOC(HDRP(bp))))
		printf("Bad epilogue header\n");
}


static void dump_bin()
{
	int index=0;
	void *bp;
	printf("\n dump bin start:\n");
	for (index = 0;index < BINSIZE; ++index)
	{
		bp = GET_PTR(bin_listp + index * WSIZE);
		if (bp != NULL) printf("In dump_bin,index:%d \n",index);
		while (bp != NULL){
			assert(PREV_FBP(bp)!=NULL);
			printblock(bp);
			printf("bp:%x\n",bp);
			printf("%x\n",PREV_FBP(bp));
			bp = GET_PTR(bp);
		}
	}
}


