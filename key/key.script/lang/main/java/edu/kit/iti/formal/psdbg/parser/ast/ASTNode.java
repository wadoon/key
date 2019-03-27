package edu.kit.iti.formal.psdbg.parser.ast;

/*-
 * #%L
 * ProofScriptParser
 * %%
 * Copyright (C) 2017 Application-oriented Formal Verification
 * %%
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as
 * published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public
 * License along with this program.  If not, see
 * <http://www.gnu.org/licenses/gpl-3.0.html>.
 * #L%
 */


import edu.kit.iti.formal.psdbg.parser.Visitable;
import edu.kit.iti.formal.psdbg.parser.Visitor;
import lombok.Getter;
import lombok.Setter;
import lombok.val;
import org.antlr.v4.runtime.ParserRuleContext;

import javax.annotation.Nullable;
import java.util.Arrays;
import java.util.Objects;

/**
 * @author Alexander Weigl
 * @version 1 (27.04.17)
 */
public abstract class ASTNode<T extends ParserRuleContext>
        implements Visitable, Copyable<ASTNode<T>> {
    /**
     * The corresponding parse rule context
     */
    protected T ruleContext;

    /**
     *
     */
    @Getter
    @Setter
    @Nullable
    protected ASTNode parent;

    /**
     *
     */
    @Getter
    protected Position startPosition = new Position();

    /**
     *
     */
    @Getter
    protected Position endPosition = new Position();

    /**
     * Returns the sourceName which defined this ast node or null
     *
     * @return
     */
    @Nullable
    public String getOrigin() {
        if (ruleContext != null) {
            String src = ruleContext.getStart().getInputStream().getSourceName();
            return src;
        }
        return null;
    }

    public T getRuleContext() {
        return ruleContext;
    }

    public void setRuleContext(T c) {
        startPosition = Position.start(c);
        endPosition = Position.end(c);
        ruleContext = c;
    }

    public Position getStartPosition() {
        return startPosition;
    }

    public Position getEndPosition() {
        return endPosition;
    }

    /**
     * <p>getNodeName.</p>
     *
     * @return a {@link java.lang.String} object.
     */
    public String getNodeName() {
        return getClass().getSimpleName();
    }

    /**
     * {@inheritDoc}
     */
    public abstract <T> T accept(Visitor<T> visitor);

    /**
     * Deep copy of the AST hierarchy.
     *
     * @return a fresh substree of the AST that is equal to this.
     */
    @Override
    public abstract ASTNode<T> copy();

    public boolean isAncestor(ASTNode node) {
        ASTNode n = this;
        do {
            if (n.equals(node))
                return true;
            n = n.getParent();
        } while (n != null);
        return true;
    }

    public boolean eq(ASTNode other) {
        return equals(other);
    }

    public int getDepth() {
        int depth = 0;
        ASTNode n = this;
        do {
            n = n.getParent();
            depth++;
        } while (n != null);
        return depth;
    }

    public ASTNode[] getChildren() {
        return new ASTNode[0];
    }

    public final ASTNode[] asList() {
        val ary = getChildren();
        val nry = Arrays.copyOf(ary, ary.length + 1);
        nry[nry.length - 1] = this;
        return nry;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;
        ASTNode<?> astNode = (ASTNode<?>) o;
        return Objects.equals(getRuleContext(), astNode.getRuleContext());
    }

    @Override
    public int hashCode() {
        return Objects.hash(getRuleContext());
    }

    //TODO: param + class
    public boolean isSame(ASTNode other) {
        return this.getNodeName().equals(other.getNodeName());
    }

    public int getSyntaxWidth() {
        if (ruleContext != null) {
            return ruleContext.stop.getStopIndex()
                    - ruleContext.start.getStartIndex();
        }
        return -1;
    }
}
