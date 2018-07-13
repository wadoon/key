/*
Copyright IBM Corp. All Rights Reserved.

SPDX-License-Identifier: Apache-2.0
*/

package org.hyperledger.fabric.shim;

public interface ChaincodeStub {
        //@ public instance ghost \seq transactionLog;

        //@ public instance model \map globalState;

        //@ represents globalState = \dl_constructMap(transactionLog);

        /*@ public normal_behaviour
            ensures \dl_array2seq(\result) == \dl_mapGet(globalState, key);
            assignable \strictly_nothing;
          @*/
	byte[] getState(int key);

        /*@ public normal_behaviour
            ensures transactionLog == \dl_seqConcat(\old(transactionLog), \dl_seqSingleton(\dl_newEntry(key,\dl_array2seq(value))));
            assignable transactionLog;
          @*/
	void putState(int key, byte[] value);

        /*@ public normal_behaviour
            ensures transactionLog == \dl_seqConcat(\old(transactionLog), \dl_seqSingleton(\dl_newEntry(key,\dl_deleted)));
            assignable transactionLog;
          @*/
	void delState(int key);


}
