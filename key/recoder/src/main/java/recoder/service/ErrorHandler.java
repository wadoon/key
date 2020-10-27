package recoder.service;

public interface ErrorHandler extends ModelUpdateListener {
    int getErrorThreshold();

    void setErrorThreshold(int paramInt);

    void reportError(Exception paramException) throws RuntimeException;
}
