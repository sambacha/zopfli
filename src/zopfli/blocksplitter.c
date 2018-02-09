/*
Copyright 2011 Google Inc. All Rights Reserved.
Copyright 2016 Mr_KrzYch00. All Rights Reserved.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

Author: lode.vandevenne@gmail.com (Lode Vandevenne)
Author: jyrki.alakuijala@gmail.com (Jyrki Alakuijala)
*/

#include "defines.h"
#include "blocksplitter.h"

#include <assert.h>
#include <stdio.h>

#include "deflate.h"
#include "squeeze.h"
#include "tree.h"
#include "util.h"

/*
The "f" for the FindMinimum function below.
i: the current parameter of f(i)
context: for your implementation
*/
typedef zfloat FindMinimumFun(size_t i, void* context);

typedef struct SplitCostContext {
  const ZopfliLZ77Store* lz77;
  const ZopfliOptions* options;
  size_t start;
  size_t end;
} SplitCostContext;

/*
Finds minimum of function f(i) where i is of type size_t, f(i) is of type
zfloat, i is in range start-end (excluding end).
Outputs the minimum value in *smallest and returns the index of this value.

Here we allow changing recursion by --bsr switch instead of using
hardcoded 9. I have no idea if it proves to be better or worse, we just
allow the user to be smarter than us.

Also prints some garbage at verbosity level 6+.
*/
static size_t FindMinimum(FindMinimumFun f, void* context,
                          size_t start, size_t end,
                          zfloat* smallest, size_t minrec) {
  SplitCostContext* c = (SplitCostContext*)context;
  size_t size = end - start;
  if (size < c->options->smallestblock) {
    zfloat best = ZOPFLI_LARGE_FLOAT;
    size_t result = start;
    size_t i;
    size_t j = end - start;
    for (i = start; i < end; i++) {
      zfloat v = f(i, context);
      if(c->options->verbose>0) fprintf(stderr,"%d \r",(int)(j--));
      if (v < best) {
        best = v;
        result = i;
      }
    }
    *smallest = best;
    return result;
  } else {
    /* Try to find minimum faster by recursively checking multiple points. */
    size_t max_recursion = 
      (c->options->mode & 0x0200) == 0x0200?
        size/minrec<2?
          2
          :size/minrec
        :minrec;
    size_t i;
    size_t *p = (size_t*)malloc(sizeof(*p) * max_recursion);
    zfloat *vp = (zfloat*)malloc(sizeof(*vp) * max_recursion);
    size_t besti;
    zfloat best;
    zfloat lastbest = ZOPFLI_LARGE_FLOAT;
    size_t pos = start;

    for (;;) {
      if (end - start <= max_recursion) break;

      for (i = 0; i < max_recursion; i++) {
        p[i] = start + (i + 1) * ((end - start) / (max_recursion + 1));
        vp[i] = f(p[i], context);
        if(c->options->verbose>0) fprintf(stderr,"%d \r",(int)(max_recursion - i));
      }
      besti = 0;
      best = vp[0];
      for (i = 1; i < max_recursion; i++) {
        if (vp[i] < best) {
          best = vp[i];
          besti = i;
        }
      }
      if (best > lastbest)
        break;

      start = besti == 0 ? start : p[besti - 1];
      end = besti == max_recursion - 1 ? end : p[besti + 1];

      pos = p[besti];
      lastbest = best;
    }
    *smallest = lastbest;
    free(p);
    free(vp);
    return pos;
  }
}

/*
Returns estimated cost of a block in bits.  It includes the size to encode the
tree and the size to encode all literal, length and distance symbols and their
extra bits.

litlens: lz77 lit/lengths
dists: ll77 distances
lstart: start of block
lend: end of block (not inclusive)
*/
static zfloat EstimateCost(const ZopfliOptions* options,
                           const ZopfliLZ77Store* lz77,
                           size_t lstart, size_t lend) {
  return ZopfliCalculateBlockSizeAutoType(options, lz77, lstart, lend, 0);
}

/*
Gets the cost which is the sum of the cost of the left and the right section
of the data.
type: FindMinimumFun
*/
static zfloat SplitCost(size_t i, void* context) {
  SplitCostContext* c = (SplitCostContext*)context;
  return EstimateCost(c->options, c->lz77, c->start, i) +
      EstimateCost(c->options, c->lz77, i, c->end);
}

static void AddSorted(size_t value, size_t** out, size_t* outsize) {
  size_t i;
  ZOPFLI_APPEND_DATA(value, out, outsize);
  for (i = 0; i + 1 < *outsize; i++) {
    if ((*out)[i] > value) {
      memmove(*out + i + 1, *out + i, (*outsize - i - 1) * sizeof(**out));
      (*out)[i] = value;
      break;
    }
  }
}

/*
Prints block split points as decimal and hex values.
*/

static void PrintPoints(size_t** splitpoints, size_t* npoints, size_t offset) {

  size_t i;

  fprintf(stderr, "Block split points: ");
  if(*npoints>0) {
    for (i = 0; i < *npoints; ++i) {
      fprintf(stderr, "%d ", (int)((*splitpoints)[i]+offset));
    }
    fprintf(stderr, "(hex:");
    for (i = 0; i < *npoints; ++i) {
      if(i==0) fprintf(stderr," "); else fprintf(stderr,",");
      fprintf(stderr, "%x", (int)((*splitpoints)[i]+offset));
    }
    fprintf(stderr,")");
  } else {
    fprintf(stderr, "NONE");
  }
  fprintf(stderr, "                 \n");

}

static void PrintBlockSplitPoints(const ZopfliLZ77Store* lz77,
                                  const size_t* lz77splitpoints,
                                  size_t nlz77points) {
  size_t* splitpoints = 0;
  size_t npoints = 0;
  size_t i;
  /* The input is given as lz77 indices, but we want to see the uncompressed
  index values. */
  size_t pos = 0;
  if (nlz77points > 0) {
    for (i = 0; i < lz77->size; i++) {
      size_t length = lz77->dists[i] == 0 ? 1 : lz77->litlens[i];
      if (lz77splitpoints[npoints] == i) {
        ZOPFLI_APPEND_DATA(pos, &splitpoints, &npoints);
        if (npoints == nlz77points) break;
      }
      pos += length;
    }
  }
  assert(npoints == nlz77points);
  PrintPoints(&splitpoints,&npoints,0);

  free(splitpoints);
}

/*
Finds next block to try to split, the largest of the available ones.
The largest is chosen to make sure that if only a limited amount of blocks is
requested, their sizes are spread evenly.
lz77size: the size of the LL77 data, which is the size of the done array here.
done: array indicating which blocks starting at that position are no longer
    splittable (splitting them increases rather than decreases cost).
splitpoints: the splitpoints found so far.
npoints: the amount of splitpoints found so far.
lstart: output variable, giving start of block.
lend: output variable, giving end of block.
returns 1 if a block was found, 0 if no block found (all are done).
*/
static int FindLargestSplittableBlock(
    size_t lz77size, const unsigned char* done,
    const size_t* splitpoints, size_t npoints,
    size_t* lstart, size_t* lend) {
  size_t longest = 0;
  int found = 0;
  size_t i;
  for (i = 0; i <= npoints; i++) {
    size_t start = i == 0 ? 0 : splitpoints[i - 1];
    size_t end = i == npoints ? lz77size - 1 : splitpoints[i];
    if (!done[start] && end - start > longest) {
      *lstart = start;
      *lend = end;
      found = 1;
      longest = end - start;
    }
  }
  return found;
}

void ZopfliBlockSplitLZ77(const ZopfliOptions* options,
                          const ZopfliLZ77Store* lz77, size_t maxblocks,
                          size_t** splitpoints, size_t* npoints) {
  size_t lstart, lend;
  size_t llpos;
  size_t numblocks;
  size_t evalsplit = (options->mode & 0x0400) == 0x0400? 1 : 0;
  size_t minrec = evalsplit?2:options->findminimumrec;
  unsigned char* done;
  zfloat splitcost;
  zfloat origcost;
  zfloat totalcost;
  zfloat totalcost2 = ZOPFLI_LARGE_FLOAT;
  size_t* splitpoints2 = 0;
  size_t npoints2 = 0;

  if (lz77->size < 10) return;  /* This code fails on tiny files. */
 
  do {
    done = (unsigned char*)calloc(lz77->size, sizeof(unsigned char));
    if (!done) exit(-1); /* Allocation failed. */
    lstart = 0;
    lend = lz77->size;
    totalcost = 0;
    numblocks = 1;
    llpos = 0;
    for (;;) {
      SplitCostContext c;

      if (maxblocks > 0 && numblocks >= maxblocks) {
        break;
      }

      c.lz77 = lz77;
      c.options = options;
      c.start = lstart;
      c.end = lend;
      assert(lstart < lend);
      llpos = FindMinimum(SplitCost, &c, lstart + 1, lend, &splitcost, minrec);

      assert(llpos > lstart);
      assert(llpos < lend);

      origcost = EstimateCost(options, lz77, lstart, lend);
      totalcost += origcost;

      if (splitcost > origcost || llpos == lstart + 1 || llpos == lend) {
        done[lstart] = 1;
      } else {
        AddSorted(llpos, &splitpoints2, &npoints2);
        ++numblocks;
        if(options->verbose>0) 
          fprintf(stderr,"      [BSR: %d] Initializing blocks: %d    \r",(int)minrec,(int)(numblocks));
      }

      if (!FindLargestSplittableBlock(
          lz77->size, done, splitpoints2, npoints2, &lstart, &lend)) {
        break;  /* No further split will probably reduce compression. */
      }

      if (lend - lstart < 10) {
        break;
      }
    }
    free(done);
    if(totalcost < totalcost2) {
      size_t i;
      if(options->verbose>0) {
        fprintf(stderr, "      [BSR: %d] %d < %d                      \n",(int)minrec,(int)totalcost,(int)totalcost2);
      }
      totalcost2 = totalcost;
      free(*splitpoints);
      *splitpoints = 0;
      *npoints = 0;
      for(i=0;i<npoints2;++i) {
        ZOPFLI_APPEND_DATA(splitpoints2[i],splitpoints,npoints);
      }
      free(splitpoints2);
      splitpoints2=0;
      npoints2 = 0;
    } 
    if(evalsplit) ++minrec;
    if(minrec > 127) evalsplit = 0;
  } while(evalsplit);

  if (options->verbose>3) {
    PrintBlockSplitPoints(lz77, *splitpoints, *npoints);
  }

  if(options->verbose>2) {
    fprintf(stderr, "Total blocks: %lu                 \n\n",(unsigned long)numblocks);
  }

}

void ZopfliBlockSplit(const ZopfliOptions* options,
                      const unsigned char* in, size_t instart, size_t inend,
                      size_t maxblocks, size_t** splitpoints, size_t* npoints) {
  size_t pos = 0;
  size_t i;
  ZopfliBlockState s;
  size_t* lz77splitpoints = 0;
  size_t nlz77points = 0;
  ZopfliLZ77Store store;
  ZopfliHash hash;
  ZopfliHash* h = &hash;

  ZopfliMallocHash(ZOPFLI_WINDOW_SIZE, h);

  ZopfliInitLZ77Store(in, &store);
  ZopfliInitBlockState(options, instart, inend, 0, &s);

  *npoints = 0;
  *splitpoints = 0;

  /* Unintuitively, Using a simple LZ77 method here instead of ZopfliLZ77Optimal
  results in better blocks. */
  ZopfliLZ77Greedy(&s, in, instart, inend, &store, h);
  ZopfliBlockSplitLZ77(options,
                       &store, maxblocks,
                       &lz77splitpoints, &nlz77points);
  /* Convert LZ77 positions to positions in the uncompressed input. */
  pos = instart;
  if (nlz77points > 0) {
    for (i = 0; i < store.size; i++) {
      size_t length = store.dists[i] == 0 ? 1 : store.litlens[i];
      if (lz77splitpoints[*npoints] == i) {
        ZOPFLI_APPEND_DATA(pos, splitpoints, npoints);
        if (*npoints == nlz77points) break;
      }
      pos += length;
    }
  }
  assert(*npoints == nlz77points);

  free(lz77splitpoints);
  ZopfliCleanHash(h);
  ZopfliCleanBlockState(&s);
  ZopfliCleanLZ77Store(&store);
}

void ZopfliBlockSplitSimple(size_t instart, size_t inend, size_t blocksize,
                            size_t** splitpoints, size_t* npoints, int verbose) {
  size_t i = instart>0? instart : blocksize;
  while (i < inend) {
    ZOPFLI_APPEND_DATA(i, splitpoints, npoints);
    i += blocksize;
  }
  if(verbose>3) PrintPoints(splitpoints,npoints,0);
  if(verbose>2) fprintf(stderr, "Total blocks: %lu                 \n\n",(unsigned long)(*npoints+1));
}
