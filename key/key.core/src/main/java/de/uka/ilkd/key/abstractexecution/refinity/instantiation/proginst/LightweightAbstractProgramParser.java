// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2010 Universitaet Karlsruhe (TH), Germany
// Universitaet Koblenz-Landau, Germany
// Chalmers University of Technology, Sweden
// Copyright (C) 2011-2020 Karlsruhe Institute of Technology, Germany
// Technical University Darmstadt, Germany
// Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//
package de.uka.ilkd.key.abstractexecution.refinity.instantiation.proginst;

import java.util.ArrayList;
import java.util.LinkedList;
import java.util.List;
import java.util.regex.MatchResult;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import de.uka.ilkd.key.abstractexecution.refinity.instantiation.exception.InvalidSyntaxException;

/**
 * @author Dominic Steinhoefel
 */
public class LightweightAbstractProgramParser {
    private final String abstrProg;

    private boolean inMlComment = false;
    private boolean inSlComment = false;
    private boolean inAEConstraint = false;
    private StringBuilder aeConstrContent;
    private int pos = 0;
    private int line = 1;
    private String subProg;
    private StringBuilder currSegment = new StringBuilder();
    private List<ProgramSegment> segments = new ArrayList<>();

    public LightweightAbstractProgramParser(final String abstrProg) {
        this.abstrProg = abstrProg;
        this.subProg = abstrProg;
    }

    /**
     * @return The list of parsed program segments, with empty ones removed and
     * comments appended to APEs. ae_constraints are not seen as comments, but
     * receive their own segment.
     */
    public List<ProgramSegment> mergedProgramSegments() {
        final LinkedList<ProgramSegment> result = new LinkedList<>();

        int i = segments.size() - 1;
        while (i >= 0) {
            if (segments.get(i).isEmptyIgnoringWhitespace()) {
                i--;
                continue;
            }

            if (segments.get(i) instanceof AbstractStatementProgramSegment) {
                AbstractStatementProgramSegment apeSeg = //
                        (AbstractStatementProgramSegment) segments.get(i);
                while (--i >= 0) {
                    if (segments.get(i).isEmptyIgnoringWhitespace()) {
                        continue;
                    } else if (segments.get(i) instanceof CommentSegment) {
                        apeSeg = apeSeg.merge((CommentSegment) segments.get(i));
                    } else {
                        break;
                    }
                }

                result.addFirst(apeSeg);
                continue;
            }

            result.addFirst(segments.get(i--));
        }

        return result;
    }

    public void parse() {
        MatchResult m;

        while (pos < abstrProg.length()) {
            if (peek("/*@")) {
                flushSegment();
                consume("/*@");
                inMlComment = true;
                continue;
            }

            if (peek("//@")) {
                if (!inMlComment) {
                    flushSegment();
                    inSlComment = true;
                }

                consume("//@");
                continue;
            }

            if (consume("\n")) {
                if (inSlComment) {
                    flushCommentSegment();
                }

                line++;
                continue;
            }

            if (consume("*/")) {
                if (inMlComment) {
                    flushCommentSegment();
                }

                continue;
            }

            if ((inMlComment || inSlComment) && consume("ae_constraint")) {
                inAEConstraint = true;
                aeConstrContent = new StringBuilder();
                continue;
            }

            if ((m = peekPattern("^\\\\abstract_statement\\s*([^;\\s]*)\\s*;")) != null) {
                flushSegment();
                consume(m);
                flushAbstractStatementSegment(m.group(1));
                continue;
            }

            if ((m = peekPattern("^\\\\abstract_expression\\s*(\\S*)\\s*(\\S*)\\b")) != null) {
                flushSegment();
                consume(m);
                flushAbstractExpressionSegment(m.group(2), m.group(1));
                continue;
            }

            if (inAEConstraint) {
                if (!peek(";") && !peek("@")) {
                    aeConstrContent.append(peek(1));
                }
            }

            if (!consume(1)) {
                if (inMlComment) {
                    throw new InvalidSyntaxException(
                            "Program end reached while in middle of multiline comment");
                }

                if (inSlComment) {
                    flushCommentSegment();
                } else {
                    flushSegment();
                }
                return;
            }
        }
    }

    private void flushAbstractExpressionSegment(final String apeName, final String apeType) {
        segments.add(new AbstractExpressionProgramSegment(currSegment.toString(), apeName, line,
                apeType));
        currSegment = new StringBuilder();
    }

    private void flushAbstractStatementSegment(final String apeName) {
        segments.add(new AbstractStatementProgramSegment(currSegment.toString(), apeName, line));
        currSegment = new StringBuilder();
    }

    private void flushCommentSegment() {
        if (inAEConstraint) {
            segments.add(new AEConstraintSegment(currSegment.toString(),
                    aeConstrContent.toString().replaceAll("\\s+", " ").trim()));
            inAEConstraint = false;
        } else {
            segments.add(new CommentSegment(currSegment.toString()));
        }

        inMlComment = false;
        inSlComment = false;

        currSegment = new StringBuilder();
    }

    private void flushSegment() {
        segments.add(new ProgramSegment(currSegment.toString()));
        currSegment = new StringBuilder();
    }

    private boolean consume(final MatchResult matcher) {
        return consume(matcher.group());
    }

    private MatchResult peekPattern(final String pattern) {
        final Pattern p = Pattern.compile(pattern);
        final Matcher matcher = p.matcher(subProg);
        return matcher.find() ? matcher.toMatchResult() : null;
    }

    private boolean peek(final String str) {
        return subProg.startsWith(str);
    }

    private boolean consume(final String str) {
        if (subProg.startsWith(str)) {
            return consume(str.length());
        }

        return false;
    }

    private String peek(int l) {
        if (subProg.length() < l) {
            return null;
        }

        return subProg.substring(0, l);
    }

    private boolean consume(int l) {
        if (subProg.length() < l) {
            return false;
        }

        pos += l;
        currSegment.append(subProg.substring(0, l));
        subProg = subProg.length() >= l ? subProg.substring(l) : "";

        return true;
    }

}
