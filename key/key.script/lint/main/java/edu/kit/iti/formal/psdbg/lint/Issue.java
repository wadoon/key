package edu.kit.iti.formal.psdbg.lint;

import lombok.Getter;

import static edu.kit.iti.formal.psdbg.lint.Level.*;

/**
 * @author Alexander Weigl
 * @version 1 (06.03.19)
 */
enum Level {WARN, INFO, ERROR}

public enum Issue {
    EMPTY_BLOCKS(INFO, "Empty blocks are useless!"),
    EQUAL_SCRIPT_NAMES(ERROR, "The identifier of scripts need to be unique.\n" +
            "{{toks.0.text}} clashes with {{toks.0.text}}."),
    NEGETED_MATCH_WITH_USING(ERROR),
    SUCC_SAME_BLOCK(WARN, "Successive blocks have no effect!"),
    THEONLY_AFTER_FOREACH(WARN),
    REDECLARE_VARIABLE(WARN),
    REDECLARE_VARIABLE_TYPE_MISMATCH(WARN),
    VARIABLE_NOT_DECLARED(WARN),
    VARIABLE_NOT_USED(WARN),
    FOREACH_AFTER_THEONLY(WARN, "{{firstToken.text}}");


    @Getter
    private final Level level;
    @Getter
    private final String message;

    Issue(Level level, String message) {
        this.level = level;
        this.message = message;
    }

    Issue(Level level) {
        this.level = level;
        this.message = null;
    }
}
