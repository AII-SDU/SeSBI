/*
 * Method A -- functional-test half of the detection matrix.
 *
 * For each of the four evaluated defect classes, we run a
 * "reasonable-effort" functional test suite: the kind of positive/typical-path
 * checks a firmware tester would naturally write when validating the feature.
 * We run each suite against BOTH the buggy and the fixed implementation.
 *
 * The point is NOT that the bug is unreachable, but that the representative
 * suite does not distinguish buggy from fixed -- i.e. conventional functional
 * testing along typical operating points passes on the buggy code. We then
 * report the specific boundary/adversarial input that WOULD be required to
 * expose the bug, which is exactly the input class a typical suite omits.
 *
 * Exit code 0 => for every bug, the representative suite gave identical
 * verdicts on buggy vs fixed (i.e. testing did not catch the bug).
 */
#include <stdint.h>
#include <stdio.h>

#define PMP_SHIFT 2

/* ---------------- Bug 1: PMP NAPOT address encoding ---------------- */
static uint64_t napot_bad(uint64_t base, unsigned l2)   { return (base >> PMP_SHIFT) | ((1ULL << (l2 - 2)) - 1); }
static uint64_t napot_fixed(uint64_t base, unsigned l2) { return (base >> PMP_SHIFT) | ((1ULL << (l2 - 3)) - 1); }
static unsigned napot_decode_l2(uint64_t a){ unsigned n=0; while(a&1){n++;a>>=1;} return n+3; }
/* region covered by a NAPOT pmpaddr: [base, base + 2^decoded_l2) */
static int napot_covers(uint64_t pmpaddr, uint64_t base, uint64_t addr){
    unsigned l2 = napot_decode_l2(pmpaddr);
    uint64_t sz = 1ULL << l2;
    return addr >= base && addr < base + sz;
}

/* ---------------- Bug 2: pmpcfg byte offset ---------------- */
static int pmpcfg_off_bad(int idx)  { return (idx % 4) * 8; }
static int pmpcfg_off_fixed(int idx){ return (idx % 8) * 8; }

/* ---------------- Bug 3: mstatus MPIE preservation ---------------- */
#define MSTATUS_MPP_MASK (3ULL << 11)
#define MSTATUS_MPIE     0x80ULL
#define PRV_S            1ULL
static uint64_t mstatus_bad(uint64_t m)  { return (m & ~MSTATUS_MPP_MASK) | (PRV_S << 11); }
static uint64_t mstatus_fixed(uint64_t m){ return mstatus_bad(m) | MSTATUS_MPIE; }
/* observable functional check a tester writes: "does MPP end up = S?" */
static int mstatus_mpp_is_S(uint64_t m){ return ((m >> 11) & 3) == PRV_S; }

/* ---------------- Bug 4: timer comparison signedness ---------------- */
static int timer_expired_bad(uint64_t cmp, uint64_t now)  { return (int64_t)cmp < (int64_t)now; }
static int timer_expired_fixed(uint64_t cmp, uint64_t now){ return cmp < now; }

int main(void){
    int suite_missed = 1; /* AND of "buggy==fixed on representative suite" */
    printf("=== Method A: functional-test half ===\n\n");

    /* ---- Bug 1: NAPOT. Representative suite: verify allowed accesses inside
       a requested region are permitted, for typical region sizes. ---- */
    {
        uint64_t base = 0x80000000ULL;
        unsigned l2 = 18;                 /* 256 KiB region, a typical map */
        uint64_t pb = napot_bad(base,l2), pf = napot_fixed(base,l2);
        /* tester probes addresses INSIDE the intended region */
        uint64_t probes[] = { base, base+4, base+1024, base+(1ULL<<l2)-1 };
        int same = 1;
        for (unsigned i=0;i<sizeof(probes)/sizeof(probes[0]);i++)
            if (napot_covers(pb,base,probes[i]) != napot_covers(pf,base,probes[i])) same=0;
        printf("[NAPOT] representative suite (in-region allow checks): buggy==fixed? %s\n", same?"YES (miss)":"NO (caught)");
        /* boundary input that WOULD catch it: address just past intended end */
        uint64_t just_past = base + (1ULL<<l2);
        printf("        boundary probe base+2^%u (0x%llx): buggy_covers=%d fixed_covers=%d  <-- needed to catch\n",
               l2,(unsigned long long)just_past, napot_covers(pb,base,just_past), napot_covers(pf,base,just_past));
        suite_missed &= same;
    }

    /* ---- Bug 2: pmpcfg offset. Representative suite: configure entries the
       firmware actually uses first, i.e. low indices 0..7. ---- */
    {
        int same = 1;
        for (int idx=0; idx<8; idx++)      /* typical: boot uses low PMP entries */
            if (pmpcfg_off_bad(idx) != pmpcfg_off_fixed(idx)) same=0;
        printf("\n[PMPCFG] representative suite (entries 0..7): buggy==fixed? %s\n", same?"YES (miss)":"NO (caught)");
        int idx=12;                        /* only entries 8..15 diverge */
        printf("        high-entry probe idx=%d: buggy_off=%d fixed_off=%d  <-- needed to catch\n",
               idx, pmpcfg_off_bad(idx), pmpcfg_off_fixed(idx));
        suite_missed &= same;
    }

    /* ---- Bug 3: mstatus MPIE. Representative suite: check the field the
       feature is "about" (MPP set to S so mret enters S-mode). ---- */
    {
        uint64_t m0 = 0;
        int same = (mstatus_mpp_is_S(mstatus_bad(m0)) == mstatus_mpp_is_S(mstatus_fixed(m0)));
        printf("\n[MSTATUS] representative suite (MPP==S after setup): buggy==fixed? %s\n", same?"YES (miss)":"NO (caught)");
        printf("        MPIE-observing probe: buggy_MPIE=%llu fixed_MPIE=%llu  <-- needed to catch\n",
               (unsigned long long)((mstatus_bad(m0)&MSTATUS_MPIE)!=0),
               (unsigned long long)((mstatus_fixed(m0)&MSTATUS_MPIE)!=0));
        suite_missed &= same;
    }

    /* ---- Bug 4: timer signedness. Representative suite: typical deadlines
       well below 2^63. ---- */
    {
        uint64_t cases[][2] = { {100,50},{1000,2000},{0xffff,0x1},{0x7fffffff,0x7ffffff0} };
        int same = 1;
        for (unsigned i=0;i<sizeof(cases)/sizeof(cases[0]);i++)
            if (timer_expired_bad(cases[i][0],cases[i][1]) != timer_expired_fixed(cases[i][0],cases[i][1])) same=0;
        printf("\n[TIMER] representative suite (deadlines < 2^63): buggy==fixed? %s\n", same?"YES (miss)":"NO (caught)");
        uint64_t cmp=0x8000000000000010ULL, now=0x7ffffffffffffff0ULL;
        printf("        high-value probe cmp>2^63 (0x%llx): buggy_expired=%d fixed_expired=%d  <-- needed to catch\n",
               (unsigned long long)cmp, timer_expired_bad(cmp,now), timer_expired_fixed(cmp,now));
        suite_missed &= same;
    }

    printf("\n=== summary: representative functional suites missed all four bugs? %s ===\n",
           suite_missed?"YES":"NO");
    return suite_missed ? 0 : 1;
}
