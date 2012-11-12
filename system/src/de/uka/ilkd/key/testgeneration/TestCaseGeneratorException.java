package de.uka.ilkd.key.testgeneration;

/**
 * Default supertype for all exceptions which can be thrown from any module in KeYTestGen
 * 
 * @author christopher
 */
public class TestCaseGeneratorException extends Exception {
    private static final long serialVersionUID = -4916814485272872541L;
    
    public TestCaseGeneratorException(String message) {
        super(message);
    }
    
    public TestCaseGeneratorException(String message, Throwable cause) {
        super(message, cause);
    }
}
