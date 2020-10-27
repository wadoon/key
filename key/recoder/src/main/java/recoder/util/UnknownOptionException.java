package recoder.util;

public class UnknownOptionException extends OptionException {
    private static final long serialVersionUID = -5505614786119000814L;

    public UnknownOptionException(String opt) {
        super(opt);
    }

    public String toString() {
        return "Unknown option \"" + this.opt + "\"";
    }
}
