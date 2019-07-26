package edu.kit.iti.formal.psdbg.interpreter.exceptions;

import edu.kit.iti.formal.psdbg.parser.ast.ASTNode;
import org.antlr.v4.runtime.ParserRuleContext;

/**
 * @author Alexander Weigl
 * @version 1 (28.05.17)
 */
public class InterpreterRuntimeException extends RuntimeException {
    private Throwable innerException = null;
    private ASTNode scriptASTNode = null;
    private String msg = "";



    public InterpreterRuntimeException() {
        super();
    }


    public String getMessage() {
        return msg;
    }

    public InterpreterRuntimeException(String message) {
        super(message);
        this.msg = message;
    }

    public InterpreterRuntimeException(String message, Throwable cause) {
        super(message, cause);
        this.msg = message;
        this.innerException = cause;
    }

    public InterpreterRuntimeException(Throwable cause) {
        super(cause);
        this.innerException = cause;
    }

    protected InterpreterRuntimeException(String message, Throwable cause, boolean enableSuppression, boolean writableStackTrace) {
        super(message, cause, enableSuppression, writableStackTrace);
        this.innerException = cause;
        this.msg = message;
    }

    public <T extends ParserRuleContext> InterpreterRuntimeException(String msg, ASTNode<T> node) {

    }

    public Throwable getInnerException() {
        return innerException;
    }

    public <T extends ParserRuleContext> ASTNode<T> getScriptASTNode() {
        return scriptASTNode;
    }

    public <T extends ParserRuleContext> InterpreterRuntimeException(Throwable cause, ASTNode<T> statement){
        super(cause);
        this.innerException = cause;
        this.scriptASTNode = statement;
    }
    public <T extends ParserRuleContext> InterpreterRuntimeException(String message, Throwable cause, ASTNode<T> statement){
        super(message, cause);
        this.innerException = cause;
        this.scriptASTNode = statement;
        this.msg= message;
    }

}
