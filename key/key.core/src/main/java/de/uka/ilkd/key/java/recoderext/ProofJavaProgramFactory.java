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


package de.uka.ilkd.key.java.recoderext;

import de.uka.ilkd.key.java.recoderext.adt.MethodSignature;
import de.uka.ilkd.key.parser.proofjava.ParseException;
import de.uka.ilkd.key.parser.proofjava.ProofJavaParser;
import recoder.ParserException;
import recoder.ServiceConfiguration;
import recoder.convenience.TreeWalker;
import recoder.io.ProjectSettings;
import recoder.io.PropertyNames;
import recoder.java.*;
import recoder.java.SourceElement.Position;
import recoder.java.declaration.*;
import recoder.java.reference.MethodReference;
import recoder.java.reference.TypeReference;
import recoder.java.reference.VariableReference;
import recoder.java.statement.Branch;
import recoder.list.generic.ASTArrayList;
import recoder.list.generic.ASTList;
import recoder.util.StringUtils;

import javax.annotation.Nonnull;
import javax.annotation.Nullable;
import java.io.IOException;
import java.io.Reader;
import java.util.ArrayList;
import java.util.LinkedList;
import java.util.List;
import java.util.Queue;

public class ProofJavaProgramFactory extends JavaProgramFactory {

    /**
     * Protected constructor - use {@link #getInstance} instead.
     */
    protected ProofJavaProgramFactory() {
    }

    /**
     * The singleton instance of the program factory.
     */
    private static ProofJavaProgramFactory theFactory
            = new ProofJavaProgramFactory();

    /**
     * Returns the single instance of this class.
     */
    public static JavaProgramFactory getInstance() {
        return theFactory;
    }

    @Override
    public void initialize(ServiceConfiguration cfg) {

        super.initialize(cfg);
        ProjectSettings settings = cfg.getProjectSettings();
      /*// that is the original recoder code:
      ProofJavaParser.setAwareOfAssert(StringUtils.parseBooleanProperty(settings.getProperties().getProperty(
              PropertyNames.JDK1_4)));
      ProofJavaParser.setJava5(ALLOW_JAVA5);
      */
        ProofJavaParser.setJava5(StringUtils.parseBooleanProperty(settings.getProperties().getProperty(
                PropertyNames.JAVA_5)));
        ProofJavaParser.setAwareOfAssert(true);

    }


    /**
     * For internal reuse and synchronization.
     */
    private static final ProofJavaParser parser = new ProofJavaParser(System.in);

    private static final Position ZERO_POSITION = new Position(0, 0);

    private static Position getPrevBlockEnd(ProgramElement pePrev, ProgramElement peNext) {
        Position startPos = peNext.getFirstElement().getStartPosition();
        ProgramElement pe = pePrev;
        Position endPos = ZERO_POSITION;
        while (pe != null) {
            if (pe.getEndPosition().compareTo(startPos) > 0) {
                return endPos;
            }
            endPos = pe.getEndPosition();
            pe = pe.getASTParent();
        }
        return endPos;
    }

    /**
     * Perform post work on the created element. Creates parent links
     * and assigns comments.
     */
    private static void postWork(@Nonnull ProgramElement programElem) {
        new PostWorkProcessor(programElem).run();
    }

    /**
     * Parse a {@link CompilationUnit} from the given reader.
     */
    @Override
    public CompilationUnit parseCompilationUnit(Reader in) throws IOException, ParserException {
        synchronized (parser) {
            try {
                ProofJavaParser.initialize(in);
                CompilationUnit res = ProofJavaParser.CompilationUnit();
                postWork(res);
                return res;
            } catch (ParseException e) {
                throw (ParserException) (new ParserException(e.getMessage())).initCause(e);
            }
        }
    }

    /**
     * Parse a {@link TypeDeclaration} from the given reader.
     */
    @Override
    public TypeDeclaration parseTypeDeclaration(Reader in) throws IOException, ParserException {
        synchronized (parser) {
            try {
                ProofJavaParser.initialize(in);
                TypeDeclaration res = ProofJavaParser.TypeDeclaration();
                postWork(res);
                return res;
            } catch (ParseException e) {
                throw (ParserException) (new ParserException(e.getMessage())).initCause(e);
            }

        }
    }

    /**
     * Parse a {@link FieldDeclaration} from the given reader.
     */
    @Override
    public FieldDeclaration parseFieldDeclaration(Reader in) throws IOException, ParserException {
        synchronized (parser) {
            try {
                ProofJavaParser.initialize(in);
                FieldDeclaration res = ProofJavaParser.FieldDeclaration();
                postWork(res);
                return res;
            } catch (ParseException e) {
                throw (ParserException) (new ParserException(e.getMessage())).initCause(e);
            }

        }
    }

    /**
     * Parse a {@link MethodDeclaration} from the given reader.
     */
    @Override
    public MethodDeclaration parseMethodDeclaration(Reader in) throws IOException, ParserException {
        synchronized (parser) {
            try {
                ProofJavaParser.initialize(in);
                MethodDeclaration res = ProofJavaParser.MethodDeclaration();
                postWork(res);
                return res;
            } catch (ParseException e) {
                throw (ParserException) (new ParserException(e.getMessage())).initCause(e);
            }

        }
    }

    /**
     * Parse a {@link MemberDeclaration} from the given reader.
     */
    @Override
    public MemberDeclaration parseMemberDeclaration(Reader in) throws IOException, ParserException {
        synchronized (parser) {
            try {
                ProofJavaParser.initialize(in);
                MemberDeclaration res = ProofJavaParser.ClassBodyDeclaration();
                postWork(res);
                return res;
            } catch (ParseException e) {
                throw (ParserException) (new ParserException(e.getMessage())).initCause(e);
            }

        }
    }

    /**
     * Parse a {@link ParameterDeclaration} from the given reader.
     */
    @Override
    public ParameterDeclaration parseParameterDeclaration(Reader in) throws IOException, ParserException {
        synchronized (parser) {
            try {
                ProofJavaParser.initialize(in);
                ParameterDeclaration res = ProofJavaParser.FormalParameter();
                postWork(res);
                return res;
            } catch (ParseException e) {
                throw (ParserException) (new ParserException(e.getMessage())).initCause(e);
            }

        }
    }

    /**
     * Parse a {@link ConstructorDeclaration} from the given reader.
     */
    @Override
    public ConstructorDeclaration parseConstructorDeclaration(Reader in) throws IOException, ParserException {
        synchronized (parser) {
            try {
                ProofJavaParser.initialize(in);
                ConstructorDeclaration res = ProofJavaParser.ConstructorDeclaration();
                postWork(res);
                return res;
            } catch (ParseException e) {
                throw (ParserException) (new ParserException(e.getMessage())).initCause(e);
            }

        }
    }

    /**
     * Parse a {@link TypeReference} from the given reader.
     */
    @Override
    public TypeReference parseTypeReference(Reader in) throws IOException, ParserException {
        synchronized (parser) {
            try {
                ProofJavaParser.initialize(in);
                TypeReference res = ProofJavaParser.ResultType();
                postWork(res);
                return res;
            } catch (ParseException e) {
                throw (ParserException) (new ParserException(e.getMessage())).initCause(e);
            }

        }
    }

    /**
     * Parse an {@link Expression} from the given reader.
     */
    @Override
    public Expression parseExpression(Reader in) throws IOException, ParserException {
        synchronized (parser) {
            try {
                ProofJavaParser.initialize(in);
                Expression res = ProofJavaParser.Expression();
                postWork(res);
                return res;
            } catch (ParseException e) {
                throw (ParserException) (new ParserException(e.getMessage())).initCause(e);
            }

        }
    }

    /**
     * Parse some {@link Statement}s from the given reader.
     */
    @Override
    public ASTList<Statement> parseStatements(Reader in) throws IOException, ParserException {
        synchronized (parser) {
            try {
                ProofJavaParser.initialize(in);
                ASTList<Statement> res = ProofJavaParser.GeneralizedStatements();
                for (int i = 0; i < res.size(); i += 1) {
                    postWork(res.get(i));
                }
                return res;
            } catch (ParseException e) {
                throw (ParserException) (new ParserException(e.getMessage())).initCause(e);
            }

        }
    }

    /**
     * Parse a {@link StatementBlock} from the given string.
     */
    @Override
    public StatementBlock parseStatementBlock(Reader in)
            throws IOException, ParserException {
        synchronized (parser) {
            try {
                ProofJavaParser.initialize(in);
                StatementBlock res = ProofJavaParser.StartBlock();
                postWork(res);
                return res;
            } catch (ParseException e) {
                throw (ParserException) (new ParserException(e.getMessage())).initCause(e);
            }

        }
    }

    /**
     * Create a {@link PassiveExpression}.
     */
    public PassiveExpression createPassiveExpression(Expression e) {
        return new PassiveExpression(e);
    }

    /**
     * Create a {@link PassiveExpression}.
     */
    public PassiveExpression createPassiveExpression() {
        return new PassiveExpression();
    }

    /**
     * Create a {@link MethodSignature}.
     */
    public MethodSignature createMethodSignature(Identifier methodName,
                                                 ASTList<TypeReference> paramTypes) {
        return new MethodSignature(methodName, paramTypes);
    }

    /**
     * Create a {@link MethodCallStatement}.
     */
    public MethodCallStatement createMethodCallStatement(Expression resVar,
                                                         ExecutionContext ec,
                                                         StatementBlock block) {
        return new MethodCallStatement(resVar, ec, block);
    }

    public LoopScopeBlock createLoopScopeBlock() {
        return new LoopScopeBlock();
    }

    public MergePointStatement createMergePointStatement() {
        return new MergePointStatement();
    }

    public MergePointStatement createMergePointStatement(Expression expr) {
        return new MergePointStatement(expr);
    }

    /**
     * Create a {@link MethodBodyStatement}.
     */
    public MethodBodyStatement createMethodBodyStatement(TypeReference bodySource,
                                                         Expression resVar,
                                                         MethodReference methRef) {
        return new MethodBodyStatement(bodySource, resVar, methRef);
    }

    /**
     * Create a {@link CatchAllStatement}.
     */
    public Statement createCatchAllStatement(VariableReference param,
                                             StatementBlock body) {
        return new CatchAllStatement(param, body);
    }

    /**
     * Create a comment.
     *
     * @param text comment text
     */
    @Override
    public Comment createComment(String text) {
        return new Comment(text);
    }

    /**
     * Create a comment.
     *
     * @param text comment text
     */
    @Override
    public Comment createComment(String text, boolean prefixed) {
        return new Comment(text, prefixed);
    }

    /**
     * Create an {@link ImplicitIdentifier}.
     */
    public ImplicitIdentifier createImplicitIdentifier(String text) {
        return new ImplicitIdentifier(text);
    }


    @Override
    public Identifier createIdentifier(String text) {
        return new ExtendedIdentifier(text);
    }

    public ObjectTypeIdentifier createObjectTypeIdentifier(String text) {
        return new ObjectTypeIdentifier(text);
    }

    public Exec createExec() {
        Exec res = new Exec();
        return res;
    }

    public Exec createExec(StatementBlock body) {
        Exec res = new Exec(body);
        return res;
    }

    public Exec createExec(StatementBlock body, ASTList<Branch> branches) {
        Exec res = new Exec(body, branches);
        return res;
    }

    public Ccatch createCcatch() {
        Ccatch res = new Ccatch();
        return res;
    }

    public Ccatch createCcatch(ParameterDeclaration e, StatementBlock body) {
        Ccatch res = new Ccatch(e, body);
        return res;
    }

    public CcatchReturnParameterDeclaration createCcatchReturnParameterDeclaration() {
        return new CcatchReturnParameterDeclaration();
    }

    public CcatchBreakParameterDeclaration createCcatchBreakParameterDeclaration() {
        return new CcatchBreakParameterDeclaration();
    }

    public CcatchBreakLabelParameterDeclaration createCcatchBreakLabelParameterDeclaration(Identifier label) {
        return new CcatchBreakLabelParameterDeclaration(label);
    }

    public CcatchBreakWildcardParameterDeclaration createCcatchBreakWildcardParameterDeclaration() {
        return new CcatchBreakWildcardParameterDeclaration();
    }

    public CcatchContinueParameterDeclaration createCcatchContinueParameterDeclaration() {
        return new CcatchContinueParameterDeclaration();
    }

    public CcatchContinueLabelParameterDeclaration createCcatchContinueLabelParameterDeclaration(Identifier label) {
        return new CcatchContinueLabelParameterDeclaration(label);
    }

    public CcatchContinueWildcardParameterDeclaration createCcatchContinueWildcardParameterDeclaration() {
        return new CcatchContinueWildcardParameterDeclaration();
    }

    public CcatchNonstandardParameterDeclaration createCcatchReturnValParameterDeclaration(ParameterDeclaration e) {
        return new CcatchReturnValParameterDeclaration(e);
    }
}

class PostWorkProcessor implements Runnable {
    private final ProgramElement programElem;
    private final List<Comment> comments;

    private final List<ProgramElement> children = new ArrayList<>(1024);

    public PostWorkProcessor(ProgramElement programElem) {
        this.programElem = programElem;
        this.comments = ProofJavaParser.getComments();

        TreeWalker tw = new TreeWalker(programElem);
        while (tw.next()) {
            children.add(tw.getProgramElement());
        }
    }

    @Override
    public void run() {
        if (!children.isEmpty()) {
            makeParentValid();
            if (!comments.isEmpty()) {
                attachComments();
            }
        }
    }

    private void makeParentValid() {
        children.stream()
                .filter(NonTerminalProgramElement.class::isInstance)
                .forEach(it -> ((NonTerminalProgramElement) it).makeParentRoleValid());
    }

    private void attachComments() {
        // This works similar to a merge algoritm.
        // We assume that `children` and `comments` are both sorted by their appearance.
        // In the core, this is a adapted merging algorithm where two sorted lists are weaved together.
        // and should be doable in O(#comments+#nodes) time.


        Queue<ProgramElement> iterNodes = new LinkedList<>(children);

        ProgramElement currentNode = null;
        ProgramElement closestParent = null;

        //simple merge algorithm
        for (Comment currentComment : comments) {
            // fixate a comment and position
            Position posComment = currentComment.getStartPosition();

            //find the next node where
            while (!iterNodes.isEmpty()) {
                currentNode = iterNodes.peek();

                if (currentNode.getFirstElement() == null) {
                    // Apparently these are nodes with no source and no position... skip them
                    continue;
                }

                Position posNode = currentNode.getFirstElement().getStartPosition();

                if (posNode.compareTo(posComment) < 0) {
                    // currentNode starts before currentComment

                    iterNodes.poll(); // go to the next node

                    // currentComment ends before currentNode, therefore currentNode wraps the currentComment
                    if (currentComment.getEndPosition().compareTo(currentNode.getEndPosition()) <= 0) {
                        closestParent = currentNode;
                    }
                } else {
                    break;
                }
            }

            //at this point, following is asserted
            // (A) pos of currentNode is the next node after comment if such node exists in children
            // (B) currentNode is non-null
            // (C) closestParent is non-null if the comment is within closestParent
            //     and there is no other "smaller" parent possible

            assert currentNode != null;
            attachComment(currentComment, currentNode, closestParent);
        }
        /*
        Position posComment = current.getFirstElement().getStartPosition();

        ProgramElement pePrev = programElem;
        ProgramElement peNext;
        TreeWalker tw = new TreeWalker(programElem);
        while (tw.next()) {
            peNext = tw.getProgramElement();
            Position startPos = peNext.getFirstElement().getStartPosition();

            if (startPos.compareTo(posComment) < 0) {
                pePrev = peNext;
                continue;
            }
            Position endPos = getPrevBlockEnd(pePrev, peNext);

            while ((commentIndex < commentCount) && endPos.compareTo(posComment) > 0) {
                // Append remaining comments to the previous block
                commentIndex = appendComments(pePrev, comments, commentIndex);
                if (commentIndex == commentCount) {
                    return;
                }
                current = comments.get(commentIndex);
                posComment = current.getFirstElement().getStartPosition();
            }
            while ((commentIndex < commentCount) && startPos.compareTo(posComment) > 0) {
                // Append comments to the next node
                current.setPrefixed(true);
                attachComment(current, peNext);
                commentIndex += 1;
                if (commentIndex == commentCount) {
                    return;
                }
                current = comments.get(commentIndex);
                posComment = current.getFirstElement().getStartPosition();
            }
            pePrev = peNext;
        }

        // Append all remaining comments to the previous block
        if (commentIndex < commentCount) {
            commentIndex = appendComments(pePrev, comments, commentIndex);
        }
         */
    }

    private void attachComment(@Nonnull Comment currentComment,
                               @Nonnull ProgramElement currentNode,
                               @Nullable ProgramElement closestParent) {
        if (closestParent != null && within(currentComment, closestParent)) {
            //DEFAULT CASE: the currentNode is the valid successor of the currentComment
            // aka both lies within the same closest parent
            if (within(currentNode, closestParent)) {
                attachComment(currentComment, currentNode);
            } else {
                // comment is the last entity in the current parent
                attachComment(currentComment, createLastStatement(closestParent));
            }
        } else {
            // This case is strange: The JML comment is outside
            // Occurs on /*@pure*/ on method declarations
            // or on comments before the class declaration
            attachComment(currentComment, currentNode);
        }
    }

    private ProgramElement createLastStatement(ProgramElement parent) {
        if (parent instanceof StatementBlock) {
            StatementBlock block = (StatementBlock) parent;
            Statement newEmpty = parent.getFactory().createEmptyStatement();
            ASTList<Statement> body = block.getBody();
            body.add(newEmpty);
            block.setBody(body);
            return newEmpty;
        }
        if (parent instanceof ClassDeclaration) {
            return parent;
        }
        assert false;
        return parent;
    }

    private boolean within(SourceElement comment, ProgramElement parent) {
        return comment.getStartPosition().compareTo(parent.getStartPosition()) >= 0
                && comment.getEndPosition().compareTo(parent.getEndPosition()) <= 0;
    }

    private static void attachComment(Comment c, ProgramElement pe) {
        ASTList<Comment> cml = pe.getComments();
        if (cml == null) {
            cml = new ASTArrayList<>();
            pe.setComments(cml);
        }
        cml.add(c);
    }
}

