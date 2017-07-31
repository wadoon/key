package de.uka.ilkd.key.speclang.translation;

/**
 * Created by jschiffl on 7/28/17.
 */
public abstract class SemanticsHelper {

    public abstract  SLExpression buildAddExpression(SLExpression left, SLExpression right) throws SLTranslationException;
    public abstract  SLExpression buildSubExpression(SLExpression left, SLExpression right) throws SLTranslationException;

    public abstract SLExpression buildUnsignedRightShiftExpression(SLExpression result, SLExpression e) throws SLTranslationException;

    public abstract SLExpression buildRightShiftExpression(SLExpression a, SLExpression e) throws SLTranslationException;

    public abstract SLExpression buildLeftShiftExpression(SLExpression result, SLExpression e) throws SLTranslationException;

    public abstract SLExpression buildMultExpression(SLExpression left, SLExpression right) throws SLTranslationException;

    public abstract SLExpression buildDivExpression(SLExpression left, SLExpression right) throws SLTranslationException;
}
