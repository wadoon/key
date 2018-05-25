/*
Copyright IBM Corp. All Rights Reserved.

SPDX-License-Identifier: Apache-2.0
*/

package org.hyperledger.fabric.shim;

public interface ChaincodeStub {


        //@ public ghost \seq transactionLog;

        //@ public model \map globalState;

        //@ represents globalState = \dl_constructMap(transactionLog);

        /*@ public normal_behaviour
            ensures \result == \dl_mapGet(globalState, key);
            assignable \strictly_nothing;
          @*/
	byte[] getState(int key);

        /*@ public normal_behaviour
            ensures transactionLog == \dl_seqConcat(\old(transactionLog), \dl_seqSingleton(\dl_newEntry(key,value)));
            assignable transactionLog;
          @*/
	void putState(String key, byte[] value);

        /*@ public normal_behaviour
            ensures transactionLog == \dl_seqConcat(\old(transactionLog), \dl_seqSingleton(\dl_newEntry(key,\dl_deleted)));
            assignable transactionLog;
          @*/
	void delState(String key);


}
