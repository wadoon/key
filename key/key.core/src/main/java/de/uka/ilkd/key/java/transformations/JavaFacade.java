// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

// This file is partially taken from the RECODER library, which is protected by
// the LGPL, and modified.


package de.uka.ilkd.key.java.transformations;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.Position;
import com.github.javaparser.ast.DataKey;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.comments.Comment;

import java.nio.charset.StandardCharsets;

public class JavaFacade {
    private static final Position ZERO_POSITION = new Position(0, 0);
    private ParserConfiguration parserConfiguration;

    public static class KeyNodeMetadata {
        NodeList<Comment> attachedComments = new NodeList<>();
    }

    private static final DataKey<KeyNodeMetadata> KEY_NODE_METADATA_DATA_KEY = new DataKey<>() {
    };

    /*
    // attaches a single comment to a Node
    private static void attachComment(Comment c, Node pe) {
        Node dest = pe;
        // never reached, proably buggy code...
        if (!c.isPrefixed()) {
            Node ppe = dest.getParentNode().get();
            int i = 0;
            if (ppe != null) {
                for (; ppe.getChildAt(i) != dest; i++) {
                }
            }
            if (i == 0) { // before syntactical parent
                c.setPrefixed(true);
            } else {
                dest = ppe.getChildAt(i - 1);
                while (dest instanceof Node) {
                    ppe = (Node) dest;
                    i = ppe.getChildCount();
                    if (i == 0) {
                        break;
                    }
                    dest = ppe.getChildAt(i - 1);
                }
            }
        }
        if (c instanceof SingleLineComment && c.isPrefixed()) {
            Position p = dest.getFirstElement().getRelativePosition();
            if (p.line < 1) {
                p.setLine(1);
                dest.getFirstElement().setRelativePosition(p);
            }
        }


        KeyNodeMetadata data;
        if (!dest.containsData(KEY_NODE_METADATA_DATA_KEY)) {
            data = new KeyNodeMetadata();
            dest.setData(KEY_NODE_METADATA_DATA_KEY, data);
        } else {
            data = dest.getData(KEY_NODE_METADATA_DATA_KEY);
        }
        data.attachedComments.add(c);
    }
*/
    /*
    // appends all comments with pos < endPos to the end of the last a block
    private static int appendComments(Node last,
                                      List<Comment> comments,
                                      int commentIndex,
                                      Position endPos) {
        int commentCount = comments.size();

        while (commentIndex < commentCount) {
            Comment current = comments.get(commentIndex);
            Position cpos = current.getRange().get().begin;

            if (endPos != null && cpos.compareTo(endPos) > 0) {
                return commentIndex;
            }

            if (!current.getText().contains("@")) {
                // "pure" comment without @ (we only need JML annotations)
                // place it somewhere, doesn't matter
                current.setPrefixed(true);
                attachComment(current, last);
                commentIndex += 1;
                continue;
            }

            Node pe = last;
            while (pe.getEndPosition().compareTo(cpos) < 0) {
                if (pe.getParentNode().get() == null) {
                    return commentIndex;
                }
                pe = pe.getParentNode().get();
            }
            if (!(pe instanceof BlockStmt)) {
                // -- conservative with old behavior of postWork --
                // Rest assured, KeY does probably some magic later
                return commentIndex;
            }
            BlockStmt block = (BlockStmt) pe;
            while (commentIndex < commentCount && pe.getEndPosition().compareTo(cpos) > 0) {
                if (current.getText().contains("@")) {
                    // append new empty statement to statement block
                    Statement newEmpty = pe.getFactory().createEmptyStatement();
                    NodeList<Statement> body = block.getBody();
                    body.add(newEmpty);
                    block.setBody(body);

                    // attach comment to empty statement
                    NodeList<Comment> cml = new NodeList<Comment>();
                    newEmpty.setComments(cml);
                    current.setPrefixed(true);
                    cml.add(current);
                } else {
                    // again, skip "pure" comments
                    current.setPrefixed(true);
                    attachComment(current, last);
                }
                commentIndex += 1;
                if (commentIndex < commentCount) {
                    current = comments.get(commentIndex);
                    cpos = current.getStartPosition();
                }
            }
        }
        return commentIndex;
    }
    private static Position getPrevBlockEnd(Node pePrev, Node peNext) {
        Position startPos = peNext.getFirstElement().getStartPosition();
        Node pe = pePrev;
        Position endPos = ZERO_POSITION;
        while (pe != null) {
            if (pe.getEndPosition().compareTo(startPos) > 0) {
                return endPos;
            }
            endPos = pe.getEndPosition();
            pe = pe.getParentNode().get();
        }
        return endPos;
    }
*/


    /**
     * Perform post work on the created element. Creates parent links
     * and assigns comments.
     */
    /*private static void postWork(Node programElem) {
        int commentIndex = 0;
        int commentCount = comments.size();
        if (commentCount == 0) {
            return;
        }
        Comment current = comments.get(commentIndex);
        Position cpos = current.getFirstElement().getStartPosition();

        Node pePrev = programElem;
        Node peNext = programElem;
        TreeWalker tw = new TreeWalker(programElem);
        while (tw.next()) {
            peNext = tw.getNode();

            if (peNext.getFirstElement() == null) {
                // Apparently, these are nodes with no source and no position... skip them
                continue;
            }

            Position startPos = peNext.getFirstElement().getStartPosition();
            if (startPos.compareTo(cpos) < 0) {
                pePrev = peNext;
                continue;
            }
            Position endPos = getPrevBlockEnd(pePrev, peNext);

            commentIndex = appendComments(pePrev, comments, commentIndex, endPos);
            if (commentIndex == commentCount) {
                return;
            }
            current = comments.get(commentIndex);
            cpos = current.getFirstElement().getStartPosition();
            while ((commentIndex < commentCount) && startPos.compareTo(cpos) > 0) {
                // Attach comments to the next node
                current.setPrefixed(true);
                attachComment(current, peNext);
                commentIndex += 1;
                if (commentIndex == commentCount) {
                    return;
                }
                current = comments.get(commentIndex);
                cpos = current.getFirstElement().getStartPosition();
            }
            pePrev = peNext;
        }
        // Append remaining comments to the previous block
        commentIndex = appendComments(pePrev, comments, commentIndex, null);

        if (commentIndex < commentCount) {
            // -- conservative with old behovior of this method ---
            // Attach all still remaining comments to the compilation unit
            Node pe = peNext;
            while (pe.getParentNode().get() != null) {
                pe = pe.getParentNode().get();
            }
            NodeList<Comment> cml = pe.getComments();
            if (cml == null) {
                pe.setComments(cml = new NodeList<Comment>());
            }
            do {
                current = comments.get(commentIndex);
                current.setPrefixed(false);
                cml.add(current);
                commentIndex += 1;
            } while (commentIndex < commentCount);
        }
    }
    */
    public void initialize() {
        this.parserConfiguration = new ParserConfiguration();
        parserConfiguration.setAttributeComments(true);
        parserConfiguration.setCharacterEncoding(StandardCharsets.UTF_8);
        parserConfiguration.setLanguageLevel(ParserConfiguration.LanguageLevel.JAVA_17);
        parserConfiguration.setLexicalPreservationEnabled(true);
        parserConfiguration.setIgnoreAnnotationsWhenAttributingComments(true);
        //parserConfiguration.addPostProcessors()
    }

    private JavaParser createJavaParser() {
        JavaParser jp = new JavaParser(parserConfiguration);
        return jp;
    }
}
