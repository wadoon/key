package org.hyperledger.fabric.shim;

/** superclass of all objects that can be stored on the ledger */
public class LedgerData {

    /*@ public normal_behaviour
      ensures \dl_array2seq(\result) == \dl_serializeLedgerData(\dl_object2LedgerData(ld));
      ensures \fresh(\result);
      assignable \nothing;                
      @*/
    public static  byte[] serialize(LedgerData ld) {
        return null;
    }

    /*@ public normal_behaviour
      ensures \dl_object2LedgerData(\result) == \dl_deserializeLedgerData(\dl_array2seq(b));
      ensures \fresh(\result);
      assignable \nothing;                
      @*/
    public static  LedgerData deserialize(byte[] b){
        return null;
    } 
}
