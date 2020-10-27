package recoder.kit;

public class NameClashException extends Exception {
    private static final long serialVersionUID = -8660164254613770539L;

    NameClashException() {
    }

    NameClashException(String msg) {
        super(msg);
    }
}
