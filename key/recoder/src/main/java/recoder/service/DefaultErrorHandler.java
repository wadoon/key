package recoder.service;

import recoder.ModelElement;
import recoder.ModelException;
import recoder.java.ProgramElement;

import java.util.EventObject;

public class DefaultErrorHandler implements ErrorHandler {
    private int errorCount = 0;

    private int errorThreshold;

    public DefaultErrorHandler() {
        setErrorThreshold(20);
    }

    public DefaultErrorHandler(int errorThreshold) {
        setErrorThreshold(errorThreshold);
    }

    protected int getErrorCount() {
        return this.errorCount;
    }

    public int getErrorThreshold() {
        return this.errorThreshold;
    }

    public void setErrorThreshold(int maxCount) {
        if (maxCount < 0)
            throw new IllegalArgumentException("Threshold should be >= 0");
        this.errorThreshold = maxCount;
    }

    protected boolean isReferingUnavailableCode(ModelElement me) {
        return false;
    }

    protected boolean isTemplateCode(ProgramElement pe) {
        return false;
    }

    protected boolean isIgnorable(Exception e) {
        if (e instanceof UnresolvedReferenceException) {
            ProgramElement unresolvedReference = ((UnresolvedReferenceException) e).getUnresolvedReference();
            if (isReferingUnavailableCode(unresolvedReference))
                return true;
            return isTemplateCode(unresolvedReference);
        }
        return false;
    }

    protected void warningMessage(Exception e) {
        String className = e.getClass().getName();
        className = className.substring(className.lastIndexOf('.') + 1);
        System.err.println("+++ Warning: " + className);
        System.err.println(e.getMessage());
        System.err.println();
    }

    protected void errorMessage(Exception e) {
        String className = e.getClass().getName();
        className = className.substring(className.lastIndexOf('.') + 1);
        System.err.println("*** " + this.errorCount + ": " + className);
        System.err.println(e.getMessage());
        System.err.println();
    }

    protected void exitAction() {
        String msg = "" + this.errorCount + " errors have occured - aborting.";
        System.err.println(msg);
        throw new ModelException(msg);
    }

    public void reportError(Exception e) {
        if (isIgnorable(e)) {
            warningMessage(e);
        } else {
            this.errorCount++;
            errorMessage(e);
            if (this.errorCount > this.errorThreshold)
                exitAction();
        }
    }

    public void modelUpdating(EventObject event) {
    }

    public void modelUpdated(EventObject event) {
        if (this.errorCount > 0)
            exitAction();
    }
}
