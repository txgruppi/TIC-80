/**********************************************************************
        C Implementation of Wu's Color Quantizer (v. 2)
        (see Graphics Gems vol. II, pp. 126-1EDGE)

Author: Xiaolin Wu
    Dept. of Computer Science
    Univ. of Western Ontario
    London, Ontario N6A 5B7
    wu@csd.uwo.ca

Algorithm: Greedy orthogonal bipartition of RGB space for variance
       minimization aided by inclusion-exclusion tricks.
       For speed no nearest neighbor search is done. Slightly
       better performance can be expected by more sophisticated
       but more expensive versions.

The author thanks Tom Lane at Tom_Lane@G.GP.CS.CMU.EDU for much of
additional documentation and a cure to a previous bug.

Free to distribute, comments and suggestions are appreciated.
**********************************************************************/ 

#include "gif.h"
#include "defines.h"

#include <stdlib.h>
#include <string.h>

#define MAXCOLOR 256
#define EDGE 33
#define CUBE_SIZE (EDGE * EDGE * EDGE)

#define RED 2
#define GREEN 1
#define BLUE 0

typedef struct {
    s32 r0;          /* min value, exclusive */
    s32 r1;          /* max value, inclusive */
    s32 g0;  
    s32 g1;  
    s32 b0;  
    s32 b1;
    s32 vol;
} box;

/* Histogram is in elements 1..HISTSIZE along each axis,
 * element 0 is for base or marginal value
 * NB: these must start out 0!
 */

static void Hist3d(vwt, vmr, vmg, vmb, m2, ir, ig, ib, size, qadd) 
/* build 3-D color histogram of counts, r/g/b, c^2 */
    s64 *vwt, *vmr, *vmg, *vmb;
    float   *m2;
    u8 *ir, *ig, *ib;
    s32 size;
    u16 *qadd;
{
    s32 ind, r, g, b;
    s32 inr, ing, inb, table[MAXCOLOR];
    s64 i;
        
    for(i=0; i<MAXCOLOR; ++i) table[i]=i*i;

    for(i=0; i<size; ++i){
        r = ir[i]; g = ig[i]; b = ib[i];
        inr=(r>>3)+1; 
        ing=(g>>3)+1; 
        inb=(b>>3)+1; 
        qadd[i]=ind=(inr<<10)+(inr<<6)+inr+(ing<<5)+ing+inb;
        /*[inr][ing][inb]*/
        ++vwt[ind];
        vmr[ind] += r;
        vmg[ind] += g;
        vmb[ind] += b;
            m2[ind] += (float)(table[r]+table[g]+table[b]);
    }
}

/* At conclusion of the histogram step, we can s32erpret
 *   wt[r][g][b] = sum over voxel of P(c)
 *   mr[r][g][b] = sum over voxel of r*P(c)  ,  similarly for mg, mb
 *   m2[r][g][b] = sum over voxel of c^2*P(c)
 * Actually each of these should be divided by 'size' to give the usual
 * s32erpretation of P() as ranging from 0 to 1, but we needn't do that here.
 */

/* We now convert histogram s32o moments so that we can rapidly calculate
 * the sums of the above quantities over any desired box.
 */


static void M3d(vwt, vmr, vmg, vmb, m2) /* compute cumulative moments. */
    s64 *vwt, *vmr, *vmg, *vmb;
    float *m2;
{
    u16 ind1, ind2;
    u8 i, r, g, b;
    s64 line, line_r, line_g, line_b,
        area[EDGE], area_r[EDGE], area_g[EDGE], area_b[EDGE];
    float line2, area2[EDGE];

    for(r=1; r<=32; ++r){

        for(i=0; i<=32; ++i) 
            area2[i]=area[i]=area_r[i]=area_g[i]=area_b[i]=0;

        for(g=1; g<=32; ++g){
            line2 = line = line_r = line_g = line_b = 0;

            for(b=1; b<=32; ++b){
                ind1 = (r<<10) + (r<<6) + r + (g<<5) + g + b; /* [r][g][b] */
                line += vwt[ind1];
                line_r += vmr[ind1]; 
                line_g += vmg[ind1]; 
                line_b += vmb[ind1];
                line2 += m2[ind1];
                area[b] += line;
                area_r[b] += line_r;
                area_g[b] += line_g;
                area_b[b] += line_b;
                area2[b] += line2;
                ind2 = ind1 - 1089; /* [r-1][g][b] */
                vwt[ind1] = vwt[ind2] + area[b];
                vmr[ind1] = vmr[ind2] + area_r[b];
                vmg[ind1] = vmg[ind2] + area_g[b];
                vmb[ind1] = vmb[ind2] + area_b[b];
                m2[ind1] = m2[ind2] + area2[b];
            }
        }
    }
}


static s64 Vol(cube, mmt) 
/* Compute sum over a box of any given statistic */
    box *cube;
    s64 mmt[EDGE][EDGE][EDGE];
{
    return( mmt[cube->r1][cube->g1][cube->b1] 
       -mmt[cube->r1][cube->g1][cube->b0]
       -mmt[cube->r1][cube->g0][cube->b1]
       +mmt[cube->r1][cube->g0][cube->b0]
       -mmt[cube->r0][cube->g1][cube->b1]
       +mmt[cube->r0][cube->g1][cube->b0]
       +mmt[cube->r0][cube->g0][cube->b1]
       -mmt[cube->r0][cube->g0][cube->b0] );
}

/* The next two routines allow a slightly more efficient calculation
 * of Vol() for a proposed subbox of a given box.  The sum of Top()
 * and Bottom() is the Vol() of a subbox split in the given direction
 * and with the specified new upper bound.
 */

static s64 Bottom(cube, dir, mmt)
/* Compute part of Vol(cube, mmt) that doesn't depend on r1, g1, or b1 */
/* (depending on dir) */
    box *cube;
    u8 dir;
    s64 mmt[EDGE][EDGE][EDGE];
{
    switch(dir){
    case RED:
        return( -mmt[cube->r0][cube->g1][cube->b1]
            +mmt[cube->r0][cube->g1][cube->b0]
            +mmt[cube->r0][cube->g0][cube->b1]
            -mmt[cube->r0][cube->g0][cube->b0] );
        break;
    case GREEN:
        return( -mmt[cube->r1][cube->g0][cube->b1]
            +mmt[cube->r1][cube->g0][cube->b0]
            +mmt[cube->r0][cube->g0][cube->b1]
            -mmt[cube->r0][cube->g0][cube->b0] );
        break;
    case BLUE:
        return( -mmt[cube->r1][cube->g1][cube->b0]
            +mmt[cube->r1][cube->g0][cube->b0]
            +mmt[cube->r0][cube->g1][cube->b0]
            -mmt[cube->r0][cube->g0][cube->b0] );
        break;
    }
}


static s64 Top(cube, dir, pos, mmt)
/* Compute remainder of Vol(cube, mmt), substituting pos for */
/* r1, g1, or b1 (depending on dir) */
    box *cube;
    u8 dir;
    s32   pos;
    s64 mmt[EDGE][EDGE][EDGE];
{
    switch(dir){
    case RED:
        return( mmt[pos][cube->g1][cube->b1] 
           -mmt[pos][cube->g1][cube->b0]
           -mmt[pos][cube->g0][cube->b1]
           +mmt[pos][cube->g0][cube->b0] );
        break;
    case GREEN:
        return( mmt[cube->r1][pos][cube->b1] 
           -mmt[cube->r1][pos][cube->b0]
           -mmt[cube->r0][pos][cube->b1]
           +mmt[cube->r0][pos][cube->b0] );
        break;
    case BLUE:
        return( mmt[cube->r1][cube->g1][pos]
           -mmt[cube->r1][cube->g0][pos]
           -mmt[cube->r0][cube->g1][pos]
           +mmt[cube->r0][cube->g0][pos] );
        break;
    }
}


static float Var(cube, m2, wt, mr, mg, mb)
/* Compute the weighted variance of a box */
/* NB: as with the raw statistics, this is really the variance * size */
    box *cube;
    float m2[EDGE][EDGE][EDGE];
    s64 wt[EDGE][EDGE][EDGE];
    s64 mr[EDGE][EDGE][EDGE];
    s64 mg[EDGE][EDGE][EDGE];
    s64 mb[EDGE][EDGE][EDGE];
{
    float dr, dg, db, xx;

    dr = Vol(cube, mr); 
    dg = Vol(cube, mg); 
    db = Vol(cube, mb);

    xx = m2[cube->r1][cube->g1][cube->b1] 
        -m2[cube->r1][cube->g1][cube->b0]
        -m2[cube->r1][cube->g0][cube->b1]
        +m2[cube->r1][cube->g0][cube->b0]
        -m2[cube->r0][cube->g1][cube->b1]
        +m2[cube->r0][cube->g1][cube->b0]
        +m2[cube->r0][cube->g0][cube->b1]
        -m2[cube->r0][cube->g0][cube->b0];

    return( xx - (dr*dr+dg*dg+db*db)/(float)Vol(cube,wt) );    
}

/* We want to minimize the sum of the variances of two subboxes.
 * The sum(c^2) terms can be ignored since their sum over both subboxes
 * is the same (the sum for the whole box) no matter where we split.
 * The remaining terms have a minus sign in the variance formula,
 * so we drop the minus sign and MAXIMIZE the sum of the two terms.
 */


static float Maximize(cube, dir, first, last, cut,
        whole_r, whole_g, whole_b, whole_w, wt, mr, mg, mb)
    box *cube;
    u8 dir;
    s32 first, last, *cut;
    s64 whole_r, whole_g, whole_b, whole_w;
    s64 wt[EDGE][EDGE][EDGE];
    s64 mr[EDGE][EDGE][EDGE];
    s64 mg[EDGE][EDGE][EDGE];
    s64 mb[EDGE][EDGE][EDGE];
{
    s64 half_r, half_g, half_b, half_w;
    s64 base_r, base_g, base_b, base_w;
    s32 i;
    float temp, max;

    base_r = Bottom(cube, dir, mr);
    base_g = Bottom(cube, dir, mg);
    base_b = Bottom(cube, dir, mb);
    base_w = Bottom(cube, dir, wt);
    max = 0.0;
    *cut = -1;
    for(i=first; i<last; ++i){
        half_r = base_r + Top(cube, dir, i, mr);
        half_g = base_g + Top(cube, dir, i, mg);
        half_b = base_b + Top(cube, dir, i, mb);
        half_w = base_w + Top(cube, dir, i, wt);
        /* now half_x is sum over lower half of box, if split at i */
        if (half_w == 0) {      /* subbox could be empty of pixels! */
          continue;             /* never split s32o an empty box */
    } else
        temp = ((float)half_r*half_r + (float)half_g*half_g +
                (float)half_b*half_b)/half_w;

    half_r = whole_r - half_r;
    half_g = whole_g - half_g;
    half_b = whole_b - half_b;
    half_w = whole_w - half_w;
        if (half_w == 0) {      /* subbox could be empty of pixels! */
          continue;             /* never split s32o an empty box */
    } else
        temp += ((float)half_r*half_r + (float)half_g*half_g +
                 (float)half_b*half_b)/half_w;

        if (temp > max) {max=temp; *cut=i;}
    }
    return(max);
}

static s32
Cut(set1, set2, wt, mr, mg, mb)
    box *set1, *set2;
    s64 wt[EDGE][EDGE][EDGE];
    s64 mr[EDGE][EDGE][EDGE];
    s64 mg[EDGE][EDGE][EDGE];
    s64 mb[EDGE][EDGE][EDGE];
{
    u8 dir;
    s32 cutr, cutg, cutb;
    float maxr, maxg, maxb;
    s64 whole_r, whole_g, whole_b, whole_w;

    whole_r = Vol(set1, mr);
    whole_g = Vol(set1, mg);
    whole_b = Vol(set1, mb);
    whole_w = Vol(set1, wt);

    maxr = Maximize(set1, RED, set1->r0+1, set1->r1, &cutr,
            whole_r, whole_g, whole_b, whole_w, wt, mr, mg, mb);
    maxg = Maximize(set1, GREEN, set1->g0+1, set1->g1, &cutg,
            whole_r, whole_g, whole_b, whole_w, wt, mr, mg, mb);
    maxb = Maximize(set1, BLUE, set1->b0+1, set1->b1, &cutb,
            whole_r, whole_g, whole_b, whole_w, wt, mr, mg, mb);

    if( (maxr>=maxg)&&(maxr>=maxb) ) {
        dir = RED;
        if (cutr < 0) return 0; /* can't split the box */
    }
    else
        if( (maxg>=maxr)&&(maxg>=maxb) ) 
            dir = GREEN;
        else
            dir = BLUE; 

    set2->r1 = set1->r1;
    set2->g1 = set1->g1;
    set2->b1 = set1->b1;

    switch (dir){
    case RED:
        set2->r0 = set1->r1 = cutr;
        set2->g0 = set1->g0;
        set2->b0 = set1->b0;
        break;
    case GREEN:
        set2->g0 = set1->g1 = cutg;
        set2->r0 = set1->r0;
        set2->b0 = set1->b0;
        break;
    case BLUE:
        set2->b0 = set1->b1 = cutb;
        set2->r0 = set1->r0;
        set2->g0 = set1->g0;
        break;
    }
    set1->vol=(set1->r1-set1->r0)*(set1->g1-set1->g0)*(set1->b1-set1->b0);
    set2->vol=(set2->r1-set2->r0)*(set2->g1-set2->g0)*(set2->b1-set2->b0);
    return 1;
}


static void Mark(cube, label, tag)
    box *cube;
    s32 label;
    u8 *tag;
{
    s32 r, g, b;

    for(r=cube->r0+1; r<=cube->r1; ++r)
       for(g=cube->g0+1; g<=cube->g1; ++g)
            for(b=cube->b0+1; b<=cube->b1; ++b)
                tag[(r<<10) + (r<<6) + r + (g<<5) + g + b] = label;
}

u32* gif_quantize(s32 size, const u8* buffer, const gif_color* palette, s32 colors)
{
    static struct
    {
        float m2[CUBE_SIZE];
        s64 wt[CUBE_SIZE];
        s64 mr[CUBE_SIZE];
        s64 mg[CUBE_SIZE];
        s64 mb[CUBE_SIZE];
    } vars;

    ZEROMEM(vars);

    u8* Ir = malloc(sizeof(u8) * size);
    u8* Ig = malloc(sizeof(u8) * size);
    u8* Ib = malloc(sizeof(u8) * size);

    for(s32 i = 0; i < size; i++)
    {
        Ir[i] = palette[buffer[i]].r;
        Ig[i] = palette[buffer[i]].g;
        Ib[i] = palette[buffer[i]].b;
    }

    u16 *Qadd = (u16*)malloc(sizeof(s16) * size);

    Hist3d(vars.wt, vars.mr, vars.mg, vars.mb, vars.m2, Ir, Ig, Ib, size, Qadd);
    free(Ig); free(Ib); free(Ir);

    M3d(vars.wt, vars.mr, vars.mg, vars.mb, vars.m2);

    static box cube[MAXCOLOR];
    cube[0].r0 = cube[0].g0 = cube[0].b0 = 0;
    cube[0].r1 = cube[0].g1 = cube[0].b1 = 32;
    s32 next = 0;

    for(s32 i = 1; i < colors; ++i)
    {
        static float vv[MAXCOLOR];

        if (Cut(&cube[next], &cube[i], vars.wt, vars.mr, vars.mg, vars.mb)) 
        {
            /* volume test ensures we won't try to cut one-cell box */
            vv[next] = (cube[next].vol > 1) ? Var(&cube[next], vars.m2, vars.wt, vars.mr, vars.mg, vars.mb) : 0.0;
            vv[i] = (cube[i].vol > 1) ? Var(&cube[i], vars.m2, vars.wt, vars.mr, vars.mg, vars.mb) : 0.0;
        }
        else
        {
            vv[next] = 0.0;   /* don't try to split this box again */
            i--;              /* didn't create box i */
        }

        next = 0; 
        float temp = vv[0];

        for(s32 k = 1; k <= i; ++k)
        {
            if (vv[k] > temp) 
            {
                temp = vv[k]; 
                next = k;
            }

            if (temp <= 0.0) 
            {
                colors = i+1;
                break;
            }            
        }
    }

    static u8 lut_r[MAXCOLOR], lut_g[MAXCOLOR], lut_b[MAXCOLOR];
    static u8 tag[CUBE_SIZE];

    for(s32 k = 0; k < colors; ++k)
    {
        Mark(&cube[k], k, tag);
        s32 weight = Vol(&cube[k], vars.wt);
        if (weight) 
        {
            lut_r[k] = Vol(&cube[k], vars.mr) / weight;
            lut_g[k] = Vol(&cube[k], vars.mg) / weight;
            lut_b[k] = Vol(&cube[k], vars.mb) / weight;
        }
        else
        {
            lut_r[k] = lut_g[k] = lut_b[k] = 0;       
        }
    }

    for(s32 i = 0; i < size; ++i)
        Qadd[i] = tag[Qadd[i]];
    /* output lut_r, lut_g, lut_b as color look-up table contents,
       Qadd as the quantized image (array of table addresses). */

    u32* result = malloc(sizeof(u32) * size);
    for(s32 i = 0; i < size; i++)
    {
        s32 index = Qadd[i];
        result[i] = (lut_b[index] << 16) + (lut_g[index] << 8) + (lut_r[index] << 0);
    }

    free(Qadd);

    return result;
}
