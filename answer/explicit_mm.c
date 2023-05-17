/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 *
 * In this naive approach, a block is allocated by simply incrementing
 * the brk pointer.  A block is pure payload. There are no headers or
 * footers.  Blocks are never coalesced or reused. Realloc is
 * implemented directly using mm_malloc and mm_free.
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
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
    "ateam",
    /* First member's full name */
    "Harry Bovik",
    /* First member's email address */
    "bovik@cs.cmu.edu",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8 // 할당되는 메모리 블록의 크기를 8의 배수로 정렬하기 위한 상수

#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7) // size를 8의 배수로 정렬하는 매크로 함수

#define SIZE_T_SIZE (ALIGN(sizeof(size_t))) // size_t 타입 변수의 크기를 8의 배수로 정렬한 크기입니다

#define WSIZE 4              // 워드와 더블워드의 크기를 각각 4바이트와 8바이트로 정의한 매크로 상수
#define DSIZE 8
#define CHUNKSIZE (1 << 12)  // 힙 확장을 위한 기본 크기 (= 초기 빈 블록의 크기)
#define MAX(x, y) ((x) > (y) ? (x) : (y)) //x와 y 중 더 큰 값을 반환하는 매크로 함수
#define PACK(size, alloc) ((size) | (alloc)) // size와 할당 비트를 결합, header와 footer에 저장할 값
#define GET(p) (*(unsigned int *)(p)) // 주소 p에 위치한 값을 읽어옵니다 (포인터라서 직접 역참조 불가능 -> 타입 캐스팅)
#define PUT(p, val) (*(unsigned int *)(p) = (val)) // 주소 p에 값을 저장합니다
#define GET_SIZE(p) (GET(p) & ~0x7) // 주소 p에 위치한 메모리 블록의 크기를 반환 사이즈 (~0x7: ...11111000, '&' 연산으로 뒤에 세자리 없어짐)
#define GET_ALLOC(p) (GET(p) & 0x1) // 주소 p에 위치한 메모리 블록의 할당 여부를 반환
#define HDRP(bp) ((char *)(bp) - WSIZE) // Header 포인터
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE) // Footer 포인터
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE))) // 다음 블록의 포인터
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE))) // 이전 블록의 포인터
#define PRED(bp) ((char *)(bp)) // 이전 블록의 bp에 들어있는 주소값을 리턴
#define SUCC(bp) ((char *)(bp + WSIZE)) // 이후 블록의 bp

static char *heap_listp = NULL; // 초기 힙 메모리 공간의 포인터를 저장하는 전역 변수
static char *free_listp; // free list의 맨 첫 블록을 가리키는 포인터
static char *find_ptr = NULL;
static void *extend_heap(size_t words); // 개수의 워드 크기만큼 힙 메모리 공간을 늘리고, 새로운 블록을 만들어 반환
static void *coalesce(void *bp); // 현재 블록 bp와 인접한 블록이 비어있으면 하나의 큰 블록으로 병합
static void *find_fit(size_t asize); // 요청한 크기 asize에 맞는 비어있는 블록을 찾아 반환
static void place(void *bp, size_t asize); // bp 블록에 asize 크기만큼의 메모리를 할당

// mm_init : 말록 패키지를 초기화

/*
 * mm_init - initialize the malloc package.
 */
int mm_init(void){
    if ((heap_listp = mem_sbrk(4*WSIZE)) == (void*) -1){ // 16바이트 만큼 확보한다. (unused + PH + PF + SUC + PRED + EH)

        return -1;
    }
    PUT(heap_listp, 0);  // unused word 4 bytes, heap_listp 주소의 key값을 0으로 입력
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE,1)); // prologue header -> (8바이트(헤더푸터), 할당됨.)
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE,1)); // prologue footer생성.

    PUT(heap_listp + (3*WSIZE), PACK(0,1)); // 에필로그 블록헤더
    find_ptr = heap_listp;  // find_ptr 은 heap_listp의 주소값을 복사한다.
    heap_listp += (2*WSIZE);

    if (extend_heap(CHUNKSIZE/WSIZE)==NULL)
        return -1;
    return 0;
}

static void *extend_heap(size_t words){
    char *bp;
    size_t size;

    /* Allocate an even number of words to maintain alignment */
    size = (words % 2) ? (words + 1) * DSIZE : words * DSIZE;
    if ((long)(bp = mem_sbrk(size)) == - 1) {
        return NULL;
    }

    /* Initialize free block header/footer and the epilogue header */
    PUT(HDRP(bp), PACK(size,0));
    PUT(FTRP(bp), PACK(size,0));
    PUT(PRED(bp), 0);
    PUT(SUCC(bp), 0);
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0,1));
    return coalesce(bp);
}

static void *find_fit(size_t asize) {
    char *get_address = GET(find_ptr);

    while (get_address != NULL) {
        if (GET_SIZE(HDRP(get_address)) >= asize) {
            return get_address;
        }
        get_address = GET(SUCC(get_address));
    }
    return NULL; // not fit any
}

static void place(void *bp, size_t asize) {
    size_t csize = GET_SIZE(HDRP(bp));
    fix_link(bp);

    if ((csize - asize) >= (2*DSIZE)) {
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize - asize, 0));
        PUT(FTRP(bp), PACK(csize - asize, 0));
        PUT(SUCC(bp), 0);
        PUT(PRED(bp), 0);
        coalesce(bp);
    }
    else {
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}

/*
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size){
    size_t asize;
    size_t extendsize;
    char *bp;

    if (size <= 0) return NULL; // 0 보다 같거나 작으면 할당해 줄 필요 없다.

    if (size <= DSIZE){
        asize = 2*DSIZE;
    }
    else {
        asize = DSIZE* ( (size + (DSIZE)+ (DSIZE-1)) / DSIZE ); // Double word allignment
    }

    if ((bp = find_fit(asize)) != NULL){ //first fit
        place(bp,asize);
        return bp;
    }
    extendsize = MAX(asize,CHUNKSIZE);
    if ( (bp=extend_heap(extendsize/DSIZE)) == NULL){
        return NULL;  // 확장이 안되면 NULL 반환해라.
    }
    place(bp,asize); //  확장이 되면 넣어라.
    return bp;
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *bp){
    size_t size = GET_SIZE(HDRP(bp));
    PUT(HDRP(bp), PACK(size,0));
    PUT(FTRP(bp), PACK(size,0));
    PUT(SUCC(bp), 0);
    PUT(PRED(bp), 0);
    coalesce(bp);
}

static void *coalesce(void *bp){
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size =  GET_SIZE(HDRP(bp));

    if (prev_alloc && next_alloc){
        // 둘다 할당 되어 있으면, free 리스트에 추가만 해주면 된다.
    }
    else if (prev_alloc && !next_alloc){
        size += GET_SIZE(HDRP(NEXT_BLKP(bp))); // 다음 블록의 헤더를 보고 그 블록의 크기만큼 지금 블록의 사이즈에 추가한다.
        fix_link(NEXT_BLKP(bp)); // 다음 블록을 합쳐주고 초기화
        PUT(HDRP(bp), PACK(size,0)); // 헤더 갱신(더 큰 크기로 PUT)
        PUT(FTRP(bp), PACK(size,0)); // 푸터 갱신
    }
    else if(!prev_alloc && next_alloc){
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        fix_link(PREV_BLKP(bp));// 이전 블록을 합쳐주고 초기화
        PUT(FTRP(bp), PACK(size,0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size,0));
        bp = PREV_BLKP(bp);
    }
    else {
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        fix_link(PREV_BLKP(bp));// 전블록
        fix_link(NEXT_BLKP(bp));// 다음블록
        PUT(HDRP(PREV_BLKP(bp)), PACK(size,0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size,0));
        bp = PREV_BLKP(bp);
    }
    add_free(bp);
    return bp;
}



/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *bp, size_t size){
    if(size <= 0){
        mm_free(bp);
        return 0;
    }
    if(bp == NULL){
        return mm_malloc(size);
    }
    void *newptr = mm_malloc(size);
    if(newptr == NULL){
        return 0;
    }
    size_t oldsize = GET_SIZE(HDRP(bp));
    if(size < oldsize){
    	oldsize = size;
	}
    memcpy(newptr, bp, oldsize);
    mm_free(bp);
    return newptr;
}

void add_free(char* ptr){
    char* succ;  // char* succ = *(unsigned int*)(find_ptr); \\         ---------------succ = **find_ptr;
    succ = GET(find_ptr);
    if (succ != 0){ // 루트에 연결 되어있는게 있을 때. // 루트가 가리키는 주소가 널이 아닐떄
        PUT(succ, ptr); // 첫 노드의 이전 항목에 지금 갱신되는 것을 넣어주고.
    }
    PUT(SUCC(ptr), succ); // ptr의 다음 노드를 첫번째 노드로 연결 시켜준다.
    PUT(find_ptr, ptr); // 루트가 가리키는 애를 새로들어온 애로 바꾼다.
}
void fix_link(char *ptr){ // fix과정은 무조건 연결을 끊어줌
    if(GET(PRED(ptr)) == NULL){ // 첫노드
        if(GET(SUCC(ptr)) != NULL){  // 다음 노드가 연결되어있으면,
            PUT(PRED(GET(SUCC(ptr))), 0); // 다음 노드의 주소의 이전 노드의 주소를 지운다.
        }
        PUT(find_ptr, GET(SUCC(ptr))); // 루트 노드가 첫 노드가 가리키던 다음 노드를 가리키게 한다.
	}
	else{ // 루트노드 이외에 다른 노드일 때
		if(GET(SUCC(ptr)) != NULL){ // 전, 후 모두 노드가 연결되어있으면
			PUT(PRED(GET(SUCC(ptr))), GET(PRED(ptr)));  // 다음노드의 주소의 이전노드값을 지금 노드의 이전값과 연결시킨다.
		}
		PUT(SUCC(GET(PRED(ptr))), GET(SUCC(ptr)));  // 이전 노드에 입력되어있던 다음 노드 주소에 지금 노드의 다음노드 주소를 넣어준다.
	}
	PUT(SUCC(ptr), 0); // 현재 노드의 SUCC, PRED 초기화
	PUT(PRED(ptr), 0);
}