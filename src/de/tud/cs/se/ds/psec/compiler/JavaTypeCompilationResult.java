package de.tud.cs.se.ds.psec.compiler;

/**
 * The result of the compilation of a Java class. Contains the compiled bytecode
 * and the internal type name for the class.
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
