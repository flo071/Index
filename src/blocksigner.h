// Copyright (c) 2017-2019 The PIVX developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#ifndef PIVX_BLOCKSIGNATURE_H
#define PIVX_BLOCKSIGNATURE_H

#include "key.h"
#include "primitives/block.h"
#include "keystore.h"
#include "wallet/wallet.h"
bool SignBlockWithKey(CBlock& block, const CKey& key);
bool SignBlock(CBlock& block, const CWallet* keystore);
bool CheckBlockSignature(const CBlock& block);

#endif //PIVX_BLOCKSIGNATURE_H