package de.uka.ilkd.key.strategy.normalization;

public class NormalizationMode {

    public enum Mode {
        SIMPLE,
        OPTIMIZED
    }

    private static Mode mode = Mode.SIMPLE;

    public static void setMode(Mode _mode) {
        mode = _mode;
    }

    public static Mode getMode() {
        return mode;
    }
}
