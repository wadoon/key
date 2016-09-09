package de.tud.cs.se.ds.psec.compiler;

/**
 * TODO
 *
 * @author Dominic Scheurer
 */
public class JavaTypeCompilationResult {
    private byte[] bytecode;
    private String internalTypeName;
    
    public JavaTypeCompilationResult(byte[] bytecode, String internalTypeName) {
        this.bytecode = bytecode;
        this.internalTypeName = internalTypeName;
    }

    public byte[] getBytecode() {
        return bytecode;
    }
    
    public String getInternalTypeName() {
        return internalTypeName;
    }
}
