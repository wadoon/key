package de.uka.ilkd.key.proof.daisy;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.rule.BuiltInRule;
import de.uka.ilkd.key.rule.DefaultBuiltInRuleApp;

public class DaisyBoundsRuleApp extends DefaultBuiltInRuleApp {

    private Term expr;

    protected DaisyBoundsRuleApp(BuiltInRule builtInRule, PosInOccurrence pio) {
        super(builtInRule, pio);
        this.expr = pio.subTerm();
    }

    public Term getExpr() {
        return expr;
    }
}