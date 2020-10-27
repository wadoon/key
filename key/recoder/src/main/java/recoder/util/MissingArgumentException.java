package recoder.util;

public class MissingArgumentException extends OptionException {
    private static final long serialVersionUID = -202835350467537194L;

    public MissingArgumentException(String opt) {
        super(opt);
    }

    public String toString() {
        return "Missing mandatory argument \"" + this.opt + "\"";
    }
}
