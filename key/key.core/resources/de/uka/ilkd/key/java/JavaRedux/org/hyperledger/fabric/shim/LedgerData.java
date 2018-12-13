package org.hyperledger.fabric.shim;

/** superclass of all objects that can be stored on the ledger */
public class LedgerData {

    /*@ public normal_behaviour
      ensures \dl_array2seq(\result) == \dl_serializeLedgerData(\dl_object2LedgerData(this));
      ensures \fresh(\result);
      assignable \nothing;
      @*/
    public byte[] /*@ helper @*/ serialize();

    /*@ public normal_behaviour
      ensures \dl_object2LedgerData(\result) == \dl_deserializeLedgerData(\dl_array2seq(b));
      ensures \fresh(\result);
      assignable \nothing;
      @*/
    public static /*@ helper @*/ LedgerData deserialize(byte[] b);
}
