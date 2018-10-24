/*
Copyright IBM Corp. All Rights Reserved.

SPDX-License-Identifier: Apache-2.0
*/

package org.hyperledger.fabric.shim;

public interface ChaincodeStub {

    //@ public instance ghost \seq transactionLog;

    /*@ public normal_behaviour
      @ ensures \dl_array2seq(\result) == \dl_getValue(\dl_lastEntry(transactionLog, key));
      @ assignable \nothing;
      @*/
    byte[] /*@ helper @*/ getState(int key);

    /*@ public normal_behaviour
      @ ensures transactionLog
      @   == \dl_seqConcat(\old(transactionLog),
      @                    \dl_seqSingleton(\dl_newEntry(key,\dl_array2seq(value))));
      @ assignable transactionLog;
      @*/
    void /*@ helper @*/ putState(int key, byte[] value);

    /*@ public normal_behaviour
      @ ensures transactionLog
      @   == \dl_seqConcat(\old(transactionLog),
      @                    \dl_seqSingleton(\dl_newEntry(key,\dl_deleted)));
      @ assignable transactionLog;
      @*/
    void /*@ helper @*/ delState(int key);

    /*@ public normal_behaviour
      @ ensures \result.length == \dl_seqLen(\dl_filterID(transactionLog, key, 0));
      @ ensures (\forall int i; 0 <= i && i < \result.length;
      @              \dl_array2seq(\result[i]) ==
      @                \dl_getValue((\dl_getEntry(\dl_filterID(transactionLog, key, 0), i)) ));
      @ assignable \nothing;
      @*/
    byte[][] /*@helper@*/ getHistoryForKey(int key);
}
