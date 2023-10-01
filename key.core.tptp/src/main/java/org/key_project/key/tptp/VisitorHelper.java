package org.key_project.key.tptp;

import de.uka.ilkd.key.tptp.tptp_v7_0_0_0BaseVisitor;
import org.antlr.v4.runtime.ParserRuleContext;
import org.antlr.v4.runtime.RuleContext;
import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

import java.util.Collection;
import java.util.List;
import java.util.stream.Collectors;

@NullMarked
public abstract class VisitorHelper<T> extends tptp_v7_0_0_0BaseVisitor<T> {
    protected @Nullable T accept(@Nullable RuleContext ctx) {
        if (ctx == null) return null;
        return (T) ctx.accept(this);
    }

    protected <T> T oneOf(ParserRuleContext... ctxs) {
        for (ParserRuleContext ctx : ctxs) {
            if (ctx != null) {
                return (T) ctx.accept(this);
            }
        }
        return null;
    }

    protected <T> List<T> mapOf(Collection<? extends ParserRuleContext> argument) {
        return argument.stream().map(it -> (T) it.accept(this)).collect(Collectors.toList());
    }

    protected void each(RuleContext... ctx) {
        for (RuleContext c : ctx) {
            accept(c);
        }
    }

    protected void each(Collection<? extends ParserRuleContext> argument) {
        for (RuleContext c : argument) {
            accept(c);
        }
    }

    @Override
    protected T aggregateResult(T aggregate, T nextResult) {
        if (nextResult != null) {
            return nextResult;
        }
        return aggregate;
    }
}
