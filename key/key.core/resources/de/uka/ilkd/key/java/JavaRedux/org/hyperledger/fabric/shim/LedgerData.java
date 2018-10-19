package org.hyperledger.fabric.shim;

/** superclass of all objects that can be stored on the ledger */
public abstract class LedgerData {

    /*@ public normal_behaviour
      ensures \dl_array2seq(\result) == \dl_serializeLedgerData(\dl_object2LedgerData(g));
      ensures \fresh(\result);
      assignable \nothing;                
      @*/
    public abstract byte[] serialize(LedgerData ld);

    /*@ public normal_behaviour
      ensures \dl_object2LedgerData(\result) == \dl_deserializeLedgerData(\dl_array2seq(bytes));
      ensures \fresh(\result);
      assignable \nothing;                
      @*/
    public abstract LedgerData deserialize(byte[] b);

}
