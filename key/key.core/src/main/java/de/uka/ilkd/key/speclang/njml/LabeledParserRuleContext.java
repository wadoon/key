package de.uka.ilkd.key.speclang.njml;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.label.OriginTermLabel;
import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.logic.origin.OriginRef;
import de.uka.ilkd.key.logic.origin.OriginRefType;
import org.antlr.v4.runtime.ParserRuleContext;
import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableSet;

import javax.annotation.Nonnull;
import javax.annotation.Nullable;
import java.util.ArrayList;

/**
 * This class maps a {@link ParserRuleContext} to a {@link TermLabel}.
 */
public class LabeledParserRuleContext {
    @Nonnull
    public final ParserRuleContext first;
    @Nullable
    public final TermLabel second;
    @Nullable
    public final OriginRef origin;

    public LabeledParserRuleContext(ParserRuleContext first, TermLabel second) {
        if (first == null) throw new IllegalArgumentException("ParserRuleContext is null");
        this.first = first;
        this.second = second;
        this.origin = null;
    }


    public LabeledParserRuleContext(ParserRuleContext first) {
        if (first == null) throw new IllegalArgumentException("ParserRuleContext is null");
        this.first = first;
        this.second = null;
        this.origin = null;
    }

    public LabeledParserRuleContext(ParserRuleContext ctx, OriginTermLabel.SpecType specType, OriginRefType refType) {
        if (ctx == null) throw new IllegalArgumentException("ParserRuleContext is null");
        this.first = ctx;
        this.second = constructTermLabel(ctx, specType);
        this.origin = constructOrigin(ctx, refType);
    }

    private static TermLabel constructTermLabel(ParserRuleContext ctx, OriginTermLabel.SpecType specType) {
        String filename = ctx.start.getTokenSource().getSourceName();
        int line = ctx.start.getLine();
        OriginTermLabel.Origin origin = new OriginTermLabel.FileOrigin(specType, filename, line);
        return new OriginTermLabel(origin);
    }

    private static OriginRef constructOrigin(ParserRuleContext ctx, OriginRefType specType) {
        String src = ctx.start.getTokenSource().getSourceName();

        return new OriginRef(src, ctx.start.getLine(), ctx.stop.getLine(), ctx.start.getStartIndex(), ctx.stop.getStopIndex(), specType);
    }

    public Term addOrigin(TermBuilder tb, Term term) {
        if (origin == null) return term;

        return tb.tf().appendOriginRef(term, ImmutableSet.singleton(origin));
    }
}
