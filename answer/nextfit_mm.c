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

static char *last_bp;
static char *heap_listp; // 초기 힙 메모리 공간의 포인터를 저장하는 전역 변수
static void *extend_heap(size_t words); // 개수의 워드 크기만큼 힙 메모리 공간을 늘리고, 새로운 블록을 만들어 반환
static void *coalesce(void *bp); // 현재 블록 bp와 인접한 블록이 비어있으면 하나의 큰 블록으로 병합
static void *find_fit(size_t asize); // 요청한 크기 asize에 맞는 비어있는 블록을 찾아 반환
static void place(void *bp, size_t asize); // bp 블록에 asize 크기만큼의 메모리를 할당


int mm_init(void)
{
    // 초기화를 위해 4 워드 크기의 힙 공간을 할당합니다.
    if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void *) -1)
        return -1;

    // 블록을 할당하기 위해 Prologue Header와 Footer를 설정합니다.
    PUT(heap_listp, 0);
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1));
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1));

    // Epilogue Header를 설정합니다.
    PUT(heap_listp + (3 * WSIZE), PACK(0, 1));

    // 힙 시작점 주소를 Prologue Header 이후로 변경합니다.
    heap_listp += (2 * WSIZE);

    // 초기 힙 확장을 시도합니다.
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL)
        return -1;

    last_bp = heap_listp;
    return 0;
}

static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;

    // 요청한 워드 수에 기반하여 메모리 크기를 계산합니다.
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;

    // mem_sbrk 함수를 사용하여 힙 확장을 시도합니다.
    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL;

    // 새 블록의 헤더와 푸터를 설정합니다.
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));

    // Epilogue Header를 설정합니다.
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));

    // 인접한 블록이 free 블록이면 coalesce 합니다.
    return coalesce(bp);
}

void *mm_malloc(size_t size)
{
    size_t asize;
    size_t extendsize;
    char *bp;

    // 할당할 크기가 0인 경우 NULL을 반환합니다.
    if (size == 0)
        return NULL;

    // 요청한 크기에 기반하여 할당할 블록의 크기를 계산합니다.
    if (size <= DSIZE)
        asize = 2 * DSIZE;
    else
        asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);
    
    // 할당 가능한 free 블록을 찾습니다.
    if ((bp = find_fit(asize)) != NULL) {
        // 찾은 블록에 할당을 진행합니다.
        place(bp, asize);
        return bp;
    }

    // 할당 가능한 free 블록을 찾지 못한 경우 힙을 확장합니다.
    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL)
        return NULL;

    // 확장한 힙에 새로운 블록을 할당합니다.
    place(bp, asize);
    return bp;
}

void mm_free(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp));

    // 블록의 헤더와 푸터에 할당 상태를 변경하여 free로 설정합니다.
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));

    // 인접한 free 블록이 있는 경우 병합(coalesce)을 수행합니다.
    coalesce(bp);
}


static void *coalesce(void *bp)
{
    // 이전 블록과 다음 블록의 할당 여부와 크기를 가져옵니다.
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && next_alloc) {
        // 이전 블록과 다음 블록이 모두 할당되어 있으면 병합하지 않고 현재 블록을 반환합니다.
        return bp;
    }

    else if (prev_alloc && !next_alloc) {
        // 이전 블록은 할당되어 있고 다음 블록은 할당되어 있지 않으면 다음 블록을 현재 블록에 통합합니다.
        // 현재 블록의 크기를 증가시키고, 헤더와 푸터를 업데이트합니다.
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }

    else if (!prev_alloc && next_alloc) {
        // 이전 블록은 할당되어 있지 않고 다음 블록은 할당되어 있으면 이전 블록을 현재 블록에 통합합니다.
        // 이전 블록의 크기를 증가시키고, 헤더와 푸터를 업데이트합니다.
        // 이전 블록의 주소를 현재 블록으로 변경합니다.
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }

    else {
        // 이전 블록과 다음 블록이 모두 할당되어 있지 않으면 이전 블록과 다음 블록을 현재 블록에 통합합니다.
        // 이전 블록과 다음 블록의 크기를 추가하여 현재 블록의 크기를 증가시키고, 헤더와 푸터를 업데이트합니다.
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }

    if ((last_bp > (char *)bp) && (last_bp < NEXT_BLKP(bp)))\
        last_bp = bp;

    return bp;
}

void *mm_realloc(void *ptr, size_t size)
{
    void *oldptr = ptr;
    void *newptr;
    size_t copySize;

    newptr = mm_malloc(size);
    if (newptr == NULL)
        return NULL;
    copySize = GET_SIZE(HDRP(oldptr));
    if (size < copySize)
        copySize = size;
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;
}

static void *find_fit(size_t asize)
{
    void *bp = last_bp;
    for (; GET_SIZE(HDRP(last_bp)) > 0; last_bp = NEXT_BLKP(last_bp)) {
        if (!GET_ALLOC(HDRP(last_bp)) && (asize <= GET_SIZE(HDRP(last_bp)))) {
            return last_bp;
        }
    }

    for (last_bp = heap_listp; last_bp < bp; last_bp = NEXT_BLKP(last_bp)) {
        if (!GET_ALLOC(HDRP(last_bp)) && (asize <= GET_SIZE(HDRP(last_bp)))) {
            return last_bp;
        }
    }

    return NULL;
}

static void place(void *bp, size_t asize) 
{
    size_t csize = GET_SIZE(HDRP(bp));

    if ((csize - asize) >= (2*DSIZE)) {
        // 남은 공간이 분할 가능한 최소 블록 크기(DSIZE)보다 크면 블록을 분할합니다.
        // 현재 블록을 할당된 상태로 표시하고 크기를 asize로 설정합니다.
        // 남은 공간을 가진 새로운 가용 블록을 생성합니다.
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize-asize, 0));
        PUT(FTRP(bp), PACK(csize-asize, 0));
    }

    else {
        // 남은 공간이 분할 가능한 최소 블록 크기(DSIZE)보다 작으면 전체 블록을 할당합니다.
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
    last_bp = bp;
}