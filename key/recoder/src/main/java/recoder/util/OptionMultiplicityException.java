package recoder.util;

public class OptionMultiplicityException extends OptionException {
    private static final long serialVersionUID = 1892377246432205468L;

    public OptionMultiplicityException(String opt) {
        super(opt);
    }

    public String toString() {
        return "Option \"" + this.opt + "\" does not allow multiple values";
    }
}
