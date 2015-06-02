/*
Copyright 2011 Google Inc. All Rights Reserved.
Copyright 2015 Mr_KrzYch00. All Rights Reserved.

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

#include "blocksplitter.h"

#include <assert.h>
#include <stdio.h>

#include "deflate.h"
#include "lz77.h"
#include "squeeze.h"
#include "tree.h"
#include "util.h"

/*
The "f" for the FindMinimum function below.
i: the current parameter of f(i)
context: for your implementation
*/
typedef double FindMinimumFun(size_t i, void* context);

/*
Finds minimum of function f(i) where is is of type size_t, f(i) is of type
double, i is in range start-end (excluding end).
*/
static size_t FindMinimum(FindMinimumFun f, void* context,
                          size_t start, size_t end, const ZopfliOptions* options) {
  if (end - start < 1024) {
    double best = ZOPFLI_LARGE_FLOAT;
    size_t result = start;
    size_t i;
    for (i = start; i < end; i++) {
      double v = f(i, context);
      if (v < best) {
        best = v;
        result = i;
      }
    }
    if(options->verbose>4) fprintf(stderr," [%lu - %lu] Best: %.0f\n",(unsigned long)start,(unsigned long)end,best);
    return result;
  } else {
    /* Try to find minimum faster by recursively checking multiple points. */
    size_t i;
    size_t *p = malloc(options->findminimumrec * sizeof(size_t));
    double *vp = malloc(options->findminimumrec * sizeof(double));
    size_t besti;
    double best;
    double lastbest = ZOPFLI_LARGE_FLOAT;
    size_t pos = start;

    for (;;) {
      if (end - start <= options->findminimumrec) break;
      for (i = 0; i < options->findminimumrec; i++) {
        p[i] = start + (i + 1) * ((end - start) / (options->findminimumrec + 1));
        vp[i] = f(p[i], context);
      }
      besti = 0;
      best = vp[0];
      for (i = 1; i < options->findminimumrec; i++) {
        if (vp[i] < best) {
          best = vp[i];
          besti = i;
        }
      }
      if (best > lastbest) {
        if(options->verbose>4) fprintf(stderr," [%lu - %lu]\n",(unsigned long)start,(unsigned long)end);
        break;
      }

      start = besti == 0 ? start : p[besti - 1];
      end = besti == options->findminimumrec - 1 ? end : p[besti + 1];

      pos = p[besti];
      lastbest = best;
      if(options->verbose>4) fprintf(stderr," [%lu - %lu] Best: %.0f\n",(unsigned long)start,(unsigned long)end,best);
    }
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
static double EstimateCost(const unsigned short* litlens,
                           const unsigned short* dists,
                           size_t lstart, size_t lend, int ohh) {
  return ZopfliCalculateBlockSize(litlens, dists, lstart, lend, 2, ohh);
}

typedef struct SplitCostContext {
  const unsigned short* litlens;
  const unsigned short* dists;
  size_t llsize;
  size_t start;
  size_t end;
  int ohh;
} SplitCostContext;


/*
Gets the cost which is the sum of the cost of the left and the right section
of the data.
type: FindMinimumFun
*/
static double SplitCost(size_t i, void* context) {
  SplitCostContext* c = (SplitCostContext*)context;
  return EstimateCost(c->litlens, c->dists, c->start, i, c->ohh) +
      EstimateCost(c->litlens, c->dists, i, c->end, c->ohh);
}

static void AddSorted(size_t value, size_t** out, size_t* outsize) {
  size_t i;
  ZOPFLI_APPEND_DATA(value, out, outsize);
  for (i = 0; i + 1 < *outsize; i++) {
    if ((*out)[i] > value) {
      size_t j;
      for (j = *outsize - 1; j > i; j--) {
        (*out)[j] = (*out)[j - 1];
      }
      (*out)[i] = value;
      break;
    }
  }
}

/*
Prints the block split points as decimal and hex values in the terminal.
*/
static void PrintBlockSplitPoints(const unsigned short* litlens,
                                  const unsigned short* dists,
                                  size_t llsize, const size_t* lz77splitpoints,
                                  size_t nlz77points, size_t offset, const char* dumpfile) {
  size_t* splitpoints = 0;
  size_t npoints = 0;
  size_t i;
  int dumpingtofile = 0;
  size_t pos = 0;
  FILE* file = NULL;
  if(dumpfile != NULL) {
    dumpingtofile = 1;
    if(fopen(dumpfile, "r")!=NULL) {
      fprintf(stderr,"Error: File %s already exists.",dumpfile);
      exit(EXIT_FAILURE);
    }
    file = fopen(dumpfile, "wb");
  }
  /* The input is given as lz77 indices, but we want to see the uncompressed
  index values. */
  if (nlz77points > 0) {
    for (i = 0; i < llsize; i++) {
      size_t length = dists[i] == 0 ? 1 : litlens[i];
      if (lz77splitpoints[npoints] == i) {
        ZOPFLI_APPEND_DATA(pos, &splitpoints, &npoints);
        if (npoints == nlz77points) break;
      }
      pos += length;
    }
  }
  assert(npoints == nlz77points);
  fprintf(stderr, "Block split points: ");
  if(dumpingtofile == 1) fprintf(file,"0");
  if(npoints>0) {
    for (i = 0; i < npoints; i++) {
      fprintf(stderr, "%d ", (int)(splitpoints[i]+offset));
    }
    fprintf(stderr, "(hex:");
    for (i = 0; i < npoints; i++) {
      if(i==0) fprintf(stderr," "); else fprintf(stderr,",");
      fprintf(stderr, "%x", (int)(splitpoints[i]+offset));
      if(dumpingtofile == 1) fprintf(file, ",%x", (int)(splitpoints[i]+offset));
    }
    fprintf(stderr,")");
  } else {
    fprintf(stderr, "NONE");
  }
  fprintf(stderr, "                 \n");

  free(splitpoints);
  if(dumpingtofile==1) {
    fprintf(stderr,"Hex split points successfully saved to file: %s\n",dumpfile);
    fclose(file);
    exit(EXIT_SUCCESS);
  }
}

/*
Finds next block to try to split, the largest of the available ones.
The largest is chosen to make sure that if only a limited amount of blocks is
requested, their sizes are spread evenly.
llsize: the size of the LL77 data, which is the size of the done array here.
done: array indicating which blocks starting at that position are no longer
    splittable (splitting them increases rather than decreases cost).
splitpoints: the splitpoints found so far.
npoints: the amount of splitpoints found so far.
lstart: output variable, giving start of block.
lend: output variable, giving end of block.
returns 1 if a block was found, 0 if no block found (all are done).
*/
static int FindLargestSplittableBlock(
    size_t llsize, const unsigned char* done,
    const size_t* splitpoints, size_t npoints,
    size_t* lstart, size_t* lend) {
  size_t longest = 0;
  int found = 0;
  size_t i;
  for (i = 0; i <= npoints; i++) {
    size_t start = i == 0 ? 0 : splitpoints[i - 1];
    size_t end = i == npoints ? llsize - 1 : splitpoints[i];
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
                          const unsigned short* litlens,
                          const unsigned short* dists,
                          size_t llsize, size_t maxblocks,
                          size_t** splitpoints, size_t* npoints, size_t* numblocks, size_t* offset) {
  size_t lstart, lend;
  size_t i;
  size_t llpos = 0;
  unsigned char* done;
  double splitcost, origcost;

  if (llsize < 10) return;  /* This code fails on tiny files. */

  done = (unsigned char*)malloc(llsize);
  if (!done) exit(-1); /* Allocation failed. */
  for (i = 0; i < llsize; i++) done[i] = 0;

  lstart = 0;
  lend = llsize;
  for (;;) {
    SplitCostContext c;

    if (maxblocks > 0 && (*numblocks) >= maxblocks) {
      break;
    }

    c.litlens = litlens;
    c.dists = dists;
    c.llsize = llsize;
    c.start = lstart;
    c.end = lend;
    c.ohh = options->optimizehuffmanheader;
    assert(lstart < lend);
    llpos = FindMinimum(SplitCost, &c, lstart + 1, lend,options);

    assert(llpos > lstart);
    assert(llpos < lend);

    splitcost = EstimateCost(litlens, dists, lstart, llpos, c.ohh) +
        EstimateCost(litlens, dists, llpos, lend, c.ohh);
    origcost = EstimateCost(litlens, dists, lstart, lend, c.ohh);

    if (splitcost > origcost || llpos == lstart + 1 || llpos == lend) {
      done[lstart] = 1;
    } else {
      AddSorted(llpos, splitpoints, npoints);
      ++(*numblocks);
      if(options->verbose>0 && options->verbose<5) fprintf(stderr,"Initializing blocks: %lu\r",(unsigned long)(*numblocks));
    }

    if (!FindLargestSplittableBlock(
        llsize, done, *splitpoints, *npoints, &lstart, &lend)) {
      break;  /* No further split will probably reduce compression. */
    }

    if (lend - lstart < 10) {
      break;
    }
  }

  if (options->verbose>3 || options->dumpsplitsfile!=NULL) {
    if(options->additionalautosplits==1) {
      PrintBlockSplitPoints(litlens, dists, llsize, *splitpoints, *npoints, *offset, NULL);
    } else {
      PrintBlockSplitPoints(litlens, dists, llsize, *splitpoints, *npoints, *offset, options->dumpsplitsfile);
    }
  }

  if(options->verbose>2 && options->additionalautosplits==0) {
    fprintf(stderr, "Total blocks: %lu                 \n\n",(unsigned long)(*numblocks));
  }


  free(done);
}

void ZopfliBlockSplit(const ZopfliOptions* options,
                      const unsigned char* in, size_t instart, size_t inend,
                      size_t maxblocks, size_t** splitpoints, size_t* npoints, size_t* numblocks) {
  size_t pos = 0;
  size_t i;
  ZopfliBlockState s;
  size_t* lz77splitpoints = 0;
  size_t nlz77points = 0;
  ZopfliLZ77Store store;

  ZopfliInitLZ77Store(&store);

  s.options = options;
  s.blockstart = instart;
  s.blockend = inend;
#ifdef ZOPFLI_LONGEST_MATCH_CACHE
  s.lmc = 0;
#endif

  *npoints = 0;
  *splitpoints = 0;

  /* Unintuitively, Using a simple LZ77 method here instead of ZopfliLZ77Optimal
  results in better blocks. */
  ZopfliLZ77Greedy(&s, in, instart, inend, &store, options);
  ZopfliBlockSplitLZ77(options,
                       store.litlens, store.dists, store.size, maxblocks,
                       &lz77splitpoints, &nlz77points, numblocks, &instart);
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
  ZopfliCleanLZ77Store(&store);
}

static void ZopfliAdditionalAutoSplitting(const ZopfliOptions* options, const unsigned char* in, size_t start, size_t end,
                                          size_t** splitpoints, size_t* npoints, size_t** blocktypes, size_t * ntypes, size_t* numblocks) {
  size_t* aassplitpoints = 0;
  size_t aasnpoints = 0;
  size_t aasnumblocks = *numblocks;
  size_t k;
  if(options->verbose>3) fprintf(stderr,"-> Additional Auto Splitting for range [%lu - %lu]:\n",(unsigned long)start,(unsigned long)end);
  ZopfliBlockSplit(options, in, start, end, 0, &aassplitpoints, &aasnpoints, &aasnumblocks);
  for(k=0;k<aasnpoints;++k) {
    ZOPFLI_APPEND_DATA(aassplitpoints[k],splitpoints, npoints);
    ZOPFLI_APPEND_DATA(2,blocktypes,ntypes);
    ++(*numblocks);
  }
  free(aassplitpoints);
}

void ZopfliBlockSplitSimple(const unsigned char* in, size_t inend,
                            size_t blocksize,
                            size_t** splitpoints, size_t* npoints, size_t** blocktypes, size_t* ntypes, const ZopfliOptions* options, unsigned long* cbs, int aas) {
  size_t i, lasti = 0;
  unsigned int j = 2;
  size_t numblocks = 1;
  int dumpingtofile = 0;
  FILE* file = NULL;
  if(options->dumpsplitsfile != NULL) {
    dumpingtofile = 1;
    if(fopen(options->dumpsplitsfile, "r")!=NULL) {
      fprintf(stderr,"Error: File %s already exists.",options->dumpsplitsfile);
      exit(EXIT_FAILURE);
    }
    file = fopen(options->dumpsplitsfile, "wb");
  }
  if(cbs==NULL) {
    i = blocksize;
  } else {
    i=cbs[2];
  }
  if(options->custblocktypes != NULL) ZOPFLI_APPEND_DATA(options->custblocktypes[1],blocktypes,ntypes);
  while (i < inend) {
    if(aas==1) ZopfliAdditionalAutoSplitting(options,in, lasti, i, splitpoints, npoints, blocktypes, ntypes, &numblocks);
    ZOPFLI_APPEND_DATA(i, splitpoints, npoints);
    if(options->custblocktypes != NULL) ZOPFLI_APPEND_DATA(options->custblocktypes[j],blocktypes,ntypes);
    if(cbs==NULL) {
      lasti = i;
      i += blocksize;
    } else {
      do {
        ++j;
        lasti=i;
        if(j>cbs[0]) {
          i=inend;
          break;
        }
        i += (cbs[j] - cbs[j-1]);
        if(i <= lasti) {
          fprintf(stderr,"Error: point [%x] lower or equal to [%x], skipping . . .\n",(int)cbs[j],(int)cbs[j-1]);
        } else if(i>=inend) {
          fprintf(stderr,"Error: point [%x] out of input data range, skipping . . .\n",(int)cbs[j]);
        }
      } while(i<=lasti);
    }
    ++numblocks;
  }
  if(aas==1 && lasti<inend) {
    ZopfliAdditionalAutoSplitting(options,in, lasti, inend, splitpoints, npoints, blocktypes, ntypes, &numblocks);
    if(options->verbose>3) fprintf(stderr,"--> SUMMARY:\n");
  }
  if(options->verbose>3 || dumpingtofile == 1) {
  if(dumpingtofile == 1) fprintf(file,"0=%d",(int)(*blocktypes)[0]);
    fprintf(stderr, "Block split points: ");
    if(*npoints>0) {
      for (j = 0; j < *npoints; j++) {
        fprintf(stderr, "%d ", (int)(*splitpoints)[j]);
      }
      fprintf(stderr, "(hex:");
      for (j = 0; j < *npoints; j++) {
        if(j==0) fprintf(stderr," "); else fprintf(stderr,",");
        fprintf(stderr, "%x", (int)(*splitpoints)[j]);
        if(dumpingtofile == 1) fprintf(file, ",%x=%d", (int)(*splitpoints)[j],(int)(*blocktypes)[j+1]);
      }
      fprintf(stderr,")");
    } else {
      fprintf(stderr, "NONE");
    }
    fprintf(stderr, "\n");
    if(dumpingtofile==1) {
      fprintf(stderr,"Hex split points successfully saved to file: %s\n",options->dumpsplitsfile);
      fclose(file);
      exit(EXIT_SUCCESS);
    }
  }
  if(options->verbose>2) {
    fprintf(stderr, "Total blocks: %lu                 \n\n",(unsigned long)numblocks);
  }
  (void)in;
}
