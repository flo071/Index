// Copyright (c) 2009-2010 Satoshi Nakamoto
// Copyright (c) 2009-2015 The Bitcoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include "pow.h"
#include "main.h"
#include "arith_uint256.h"
#include "chain.h"
#include "primitives/block.h"
#include "consensus/consensus.h"
#include "uint256.h"
#include <iostream>
#include "util.h"
#include "chainparams.h"
#include "libzerocoin/bitcoin_bignum/bignum.h"
#include "utilstrencodings.h"
#include "crypto/MerkleTreeProof/mtp.h"
#include "mtpstate.h"
#include "fixed.h"
 bool USE_LWMA = false;
 bool USE_DGW3 =true;
static CBigNum bnProofOfWorkLimit(~arith_uint256(0) >> 8);

double GetDifficultyHelper(unsigned int nBits) {
    int nShift = (nBits >> 24) & 0xff;
    double dDiff = (double) 0x0000ffff / (double) (nBits & 0x00ffffff);

    while (nShift < 29) {
        dDiff *= 256.0;
        nShift++;
    }
    while (nShift > 29) {
        dDiff /= 256.0;
        nShift--;
    }

    return dDiff;
}

unsigned int static DarkGravityWave(const CBlockIndex* pindexLast, const CBlockHeader *pblock, const Consensus::Params& params,bool fProofOfStake) {
 /* current difficulty formula, veil - DarkGravity v3, written by Evan Duffield - evan@dash.org */
    const arith_uint256 bnPowLimit = UintToArith256(params.powLimit);

    const CBlockIndex *pindex = pindexLast;
    const CBlockIndex* pindexLastMatchingProof = nullptr;
    arith_uint256 bnPastTargetAvg = 0;

    unsigned int nCountBlocks = 0;
    while (nCountBlocks < 15) {
        // Ran out of blocks, return pow limit
        if (!pindex)
            return bnPowLimit.GetCompact();

        // Only consider PoW or PoS blocks but not both
        if (pindex->IsProofOfStake() != fProofOfStake) {
            pindex = pindex->pprev;
            continue;
        } else if (!pindexLastMatchingProof) {
            pindexLastMatchingProof = pindex;
        }

        arith_uint256 bnTarget = arith_uint256().SetCompact(pindex->nBits);
        bnPastTargetAvg = (bnPastTargetAvg * nCountBlocks + bnTarget) / (nCountBlocks + 1);

        if (++nCountBlocks != 15)
            pindex = pindex->pprev;
    }

    arith_uint256 bnNew(bnPastTargetAvg);

    //Should only happen on the first PoS block
    if (pindexLastMatchingProof)
        pindexLastMatchingProof = pindexLast;

    int64_t nActualTimespan = pindexLastMatchingProof->GetBlockTime() - pindex->GetBlockTime();
    int64_t nTargetTimespan = 15 * params.nPowTargetSpacing;

    if (nActualTimespan < nTargetTimespan/3)
        nActualTimespan = nTargetTimespan/3;
    if (nActualTimespan > nTargetTimespan*3)
        nActualTimespan = nTargetTimespan*3;

    // Retarget
    bnNew *= nActualTimespan;
    bnNew /= nTargetTimespan;

    if (bnNew > bnPowLimit) {
        bnNew = bnPowLimit;
    }

    return bnNew.GetCompact();
}
unsigned int LwmaCalculateNextWorkRequired(const CBlockIndex* pindexPrev, const CBlockHeader *pblock, const Consensus::Params& params) 
{

    // This cannot handle the genesis block and early blocks in general.
    assert(pindexPrev);
    
    // Special difficulty rule for testnet:
    // If the new block's timestamp is more than 2* 10 minutes then allow
    // mining of a min-difficulty block.
    if (params.fPowAllowMinDifficultyBlocks &&
        (pblock->GetBlockTime() >
         pindexPrev->GetBlockTime() + 10 * params.nPowTargetSpacing)) {
        return UintToArith256(params.powLimit).GetCompact();
    }
  
    const int nHeight = pindexPrev->nHeight + 1;
  
    // Don't adjust difficult until we have a full window worth
    // this means we should also start the starting value
    // to a reasonable level !
    if (nHeight <= params.nZawyLwmaAveragingWindow) {
      return UintToArith256(params.powLimit).GetCompact();
    }
  
    const int64_t T = params.nPowTargetSpacing;
    const int N = params.nZawyLwmaAveragingWindow;
    const int k = (N+1) * T / 2;  // ignore adjust 0.9989^(500/N) from python code
    const int dnorm = 10;

    arith_uint256 sum_target;
    int t = 0, j = 0;

    // Loop through N most recent blocks.
    for (int i = nHeight - N; i < nHeight; i++) {
        const CBlockIndex* block = pindexPrev->GetAncestor(i);
        const CBlockIndex* block_Prev = block->GetAncestor(i - 1);
        int64_t solvetime = block->GetBlockTime() - block_Prev->GetBlockTime();

        solvetime = std::min(6*T, solvetime);

        j++;
        t += solvetime * j;  // Weighted solvetime sum.

        // Target sum divided by a factor, (k N^2).
        // The factor is a part of the final equation. However we divide sum_target here to avoid
        // potential overflow.
        arith_uint256 target;
        target.SetCompact(block->nBits);
        sum_target += target / (k * N * N);
    }
    // Keep t reasonable in case strange solvetimes occurred.
    if (t < N * k / dnorm) {
        t = N * k / dnorm;
    }

    const arith_uint256 pow_limit = UintToArith256(params.powLimit);
    arith_uint256 next_target = t * sum_target;
    if (next_target > pow_limit) {
        next_target = pow_limit;
    }

    return next_target.GetCompact();
}

unsigned int GetNextWorkRequired(const CBlockIndex *pindexLast, const CBlockHeader *pblock, const Consensus::Params &params, bool fProofOfStake) {
    // Special rule for regtest: we never retarget.
    if (params.fPowNoRetargeting) {
        return pindexLast->nBits;
    }
    if(USE_DGW3)
       return DarkGravityWave(pindexLast, pblock, params,fProofOfStake);
    else if (USE_LWMA)
       return LwmaCalculateNextWorkRequired(pindexLast, pblock, params);

}

unsigned int CalculateNextWorkRequired(const CBlockIndex *pindexLast, int64_t nFirstBlockTime, const Consensus::Params &params) {
    if (params.fPowNoRetargeting)
        return pindexLast->nBits;

    // Limit adjustment step
    int64_t nActualTimespan = pindexLast->GetBlockTime() - nFirstBlockTime;
    if (nActualTimespan < params.nPowTargetTimespan / 4)
        nActualTimespan = params.nPowTargetTimespan / 4;
    if (nActualTimespan > params.nPowTargetTimespan * 4)
        nActualTimespan = params.nPowTargetTimespan * 4;

    // Retarget
    const arith_uint256 bnPowLimit = UintToArith256(params.powLimit);
    arith_uint256 bnNew;
    bnNew.SetCompact(pindexLast->nBits);
    bnNew *= nActualTimespan;
    bnNew /= params.nPowTargetTimespan;

    if (bnNew > bnPowLimit)
        bnNew = bnPowLimit;

    return bnNew.GetCompact();
}

// Index - MTP
bool CheckMerkleTreeProof(const CBlockHeader &block, const Consensus::Params &params) {
    if (!block.IsMTP())
        return true;

    if (!block.mtpHashData)
        return false;

    uint256 calculatedMtpHashValue;
    bool isVerified = mtp::verify(block.nNonce, block, Params().GetConsensus().powLimit, &calculatedMtpHashValue) &&
                      block.mtpHashValue == calculatedMtpHashValue;

    if(!isVerified)
        return false;

    return true;
}

bool CheckProofOfWork(uint256 hash, unsigned int nBits, const Consensus::Params &params) {
    bool fNegative;
    bool fOverflow;
    arith_uint256 bnTarget;
    bnTarget.SetCompact(nBits, &fNegative, &fOverflow);
    // Check range
    if (fNegative || bnTarget == 0 || fOverflow || bnTarget > UintToArith256(params.powLimit)){
        return false;
    }
        // Check proof of work matches claimed amount
        if (UintToArith256(hash) > bnTarget){
           return error("CheckProofOfWork() : hash doesn't match nBits\n");
        }
    return true;
}