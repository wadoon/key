package org.hyperledger.fabric.shim;

/** superclass of all objects that can be stored on the ledger */
public abstract class LedgerData {

    public abstract byte[] serialize(LedgerData ld);

    public abstract LedgerData deserialize(byte[] b);

}
