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

package de.uka.ilkd.key.util.joinrule;

import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;

import org.key_project.util.collection.ImmutableSet;

import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.declaration.*;
import de.uka.ilkd.key.java.expression.ArrayInitializer;
import de.uka.ilkd.key.java.expression.ParenthesizedExpression;
import de.uka.ilkd.key.java.expression.PassiveExpression;
import de.uka.ilkd.key.java.expression.literal.*;
import de.uka.ilkd.key.java.expression.operator.*;
import de.uka.ilkd.key.java.expression.operator.adt.*;
import de.uka.ilkd.key.java.reference.*;
import de.uka.ilkd.key.java.statement.*;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.rule.AbstractProgramElement;
import de.uka.ilkd.key.rule.metaconstruct.ProgramTransformer;
import de.uka.ilkd.key.speclang.BlockContract;
import de.uka.ilkd.key.speclang.LoopInvariant;

/**
 * Extends the JavaASTWalker to use the visitor mechanism. The methods inherited
 * by the Visitor interface are all implemented that they call the method
 * <code> doDefaultAction(ProgramElement) </code>.
 * 
 * TODO: Document (also, if sensible, containing methods!).
 *
 * @author Dominic Scheurer
 */
public abstract class SimultaneousJavaASTVisitor extends
        SimultaneousJavaASTWalker implements SimultaneousVisitor {

    protected final Services services;

    /**
     * create the JavaASTVisitor
     * 
     * @param root
     *            the ProgramElement where to begin
     */
    public SimultaneousJavaASTVisitor(ProgramElement e1, ProgramElement e2,
            Services services) {
        super(e1, e2);
        this.services = services;
    }

    protected void walk(ProgramElement node1, ProgramElement node2) {
        super.walk(node1, node2);

        if (node1 instanceof LoopStatement && services != null) {
            LoopInvariant li = services.getSpecificationRepository()
                    .getLoopInvariant((LoopStatement) node1);
            if (li != null) {
                visit(li);
            }
        }
        else if (node1 instanceof StatementBlock && services != null) {
            ImmutableSet<BlockContract> bcs = services
                    .getSpecificationRepository().getBlockContracts(
                            (StatementBlock) node1);
            for (BlockContract bc : bcs) {
                visit(bc);
            }
        }
    }

    /**
     * The action that is performed just before leaving the node the last time.
     *
     * @param node1 First node.
     * @param node2 Second node.
     */
    protected void doAction(ProgramElement node1, ProgramElement node2) {
        Class<? extends ProgramElement> theClass = node1.getClass();
        
        assert theClass.equals(node2.getClass());

        Method m = null;
        try {
            m = this.getClass().getMethod("visit",
                    theClass, theClass);
        }
        catch (NoSuchMethodException e) {
//            throw new IllegalArgumentException(
//                    "This method can't handle objects of type: "
//                            + node1.getClass(), e);
            System.err.println("This method can't handle objects of type: "
                  + node1.getClass());
            return;
        }
        
        try {
            m.invoke(this, node1, node2); // "<==>" visit(node1, node2);
        }
        catch (IllegalAccessException e) {
            // Shouldn't happen
            throw new RuntimeException(e);
        }
        catch (IllegalArgumentException e) {
            // Shouldn't happen
            throw new RuntimeException(e);
        }
        catch (InvocationTargetException e) {
            // Shouldn't happen. Still this is the most probable
            // exception to be thrown, in case that the visitor
            // throws an exception.
            throw new RuntimeException(e);
        }
    }
    
    /**
     * The (default) action that is performed just before leaving the node the last time.
     *
     * @param node1 First node.
     * @param node2 Second node.
     */
    protected abstract void doDefaultAction(SourceElement node1,
            SourceElement node2);

    @Override
    public void visit(AbstractProgramElement x1, AbstractProgramElement x2) {
        doDefaultAction(x1, x2);
    }

    @Override
    public void visit(ArrayDeclaration x1, ArrayDeclaration x2) {
        doDefaultAction(x1, x2);
    }

    @Override
    public void visit(ArrayInitializer x1, ArrayInitializer x2) {
        doDefaultAction(x1, x2);
    }

    @Override
    public void visit(ArrayLengthReference x1, ArrayLengthReference x2) {
        doDefaultAction(x1, x2);
    }

    @Override
    public void visit(ArrayReference x1, ArrayReference x2) {
        doDefaultAction(x1, x2);
    }

    @Override
    public void visit(Assert x1, Assert x2) {
        doDefaultAction(x1, x2);
    }

    @Override
    public void visit(BinaryAnd x1, BinaryAnd x2) {
        doDefaultAction(x1, x2);
    }

    @Override
    public void visit(BinaryAndAssignment x1, BinaryAndAssignment x2) {
        doDefaultAction(x1, x2);
    }

    @Override
    public void visit(BinaryNot x1, BinaryNot x2) {
        doDefaultAction(x1, x2);
    }

    @Override
    public void visit(BinaryOr x1, BinaryOr x2) {
        doDefaultAction(x1, x2);
    }

    @Override
    public void visit(BinaryOrAssignment x1, BinaryOrAssignment x2) {
        doDefaultAction(x1, x2);
    }

    @Override
    public void visit(BinaryXOr x1, BinaryXOr x2) {
        doDefaultAction(x1, x2);
    }

    @Override
    public void visit(BinaryXOrAssignment x1, BinaryXOrAssignment x2) {
        doDefaultAction(x1, x2);
    }

    @Override
    public void visit(BooleanLiteral x1, BooleanLiteral x2) {
        doDefaultAction(x1, x2);
    }

    @Override
    public void visit(EmptySetLiteral x1, EmptySetLiteral x2) {
        doDefaultAction(x1, x2);
    }

    @Override
    public void visit(Singleton x1, Singleton x2) {
        doDefaultAction(x1, x2);
    }

    @Override
    public void visit(SetUnion x1, SetUnion x2) {
        doDefaultAction(x1, x2);
    }

    @Override
    public void visit(Intersect x1, Intersect x2) {
        doDefaultAction(x1, x2);
    }

    @Override
    public void visit(SetMinus x1, SetMinus x2) {
        doDefaultAction(x1, x2);
    }

    @Override
    public void visit(AllFields x1, AllFields x2) {
        doDefaultAction(x1, x2);
    }

    @Override
    public void visit(AllObjects x1, AllObjects x2) {
        doDefaultAction(x1, x2);
    }

    @Override
    public void visit(EmptySeqLiteral x1, EmptySeqLiteral x2) {
        doDefaultAction(x1, x2);
    }

    @Override
    public void visit(SeqSingleton x1, SeqSingleton x2) {
        doDefaultAction(x1, x2);
    }

    @Override
    public void visit(SeqConcat x1, SeqConcat x2) {
        doDefaultAction(x1, x2);
    }

    @Override
    public void visit(SeqSub x1, SeqSub x2) {
        doDefaultAction(x1, x2);
    }

    @Override
    public void visit(SeqReverse x1, SeqReverse x2) {
        doDefaultAction(x1, x2);
    }

    @Override
    public void visit(DLEmbeddedExpression x1, DLEmbeddedExpression x2) {
        doDefaultAction(x1, x2);
    }

    @Override
    public void visit(SeqIndexOf x1, SeqIndexOf x2) {
        doDefaultAction(x1, x2);
    }

    @Override
    public void visit(SeqGet x1, SeqGet x2) {
        doDefaultAction(x1, x2);
    }

    @Override
    public void visit(SeqLength x1, SeqLength x2) {
        doDefaultAction(x1, x2);
    }

    @Override
    public void visit(Break x1, Break x2) {
        doDefaultAction(x1, x2);
    }

    @Override
    public void visit(Case x1, Case x2) {
        doDefaultAction(x1, x2);
    }

    @Override
    public void visit(Catch x1, Catch x2) {
        doDefaultAction(x1, x2);
    }

    @Override
    public void visit(CatchAllStatement x1, CatchAllStatement x2) {
        doDefaultAction(x1, x2);
    }

    @Override
    public void visit(CharLiteral x1, CharLiteral x2) {
        doDefaultAction(x1, x2);
    }

    @Override
    public void visit(ClassDeclaration x1, ClassDeclaration x2) {
        doDefaultAction(x1, x2);
    }

    @Override
    public void visit(ClassInitializer x1, ClassInitializer x2) {
        doDefaultAction(x1, x2);
    }

    @Override
    public void visit(Comment x1, Comment x2) {
        doDefaultAction(x1, x2);
    }

    @Override
    public void visit(CompilationUnit x1, CompilationUnit x2) {
        doDefaultAction(x1, x2);
    }

    @Override
    public void visit(Conditional x1, Conditional x2) {
        doDefaultAction(x1, x2);
    }

    @Override
    public void visit(ConstructorDeclaration x1, ConstructorDeclaration x2) {
        doDefaultAction(x1, x2);
    }

    @Override
    public void visit(ContextStatementBlock x1, ContextStatementBlock x2) {
        doDefaultAction(x1, x2);
    }

    @Override
    public void visit(Continue x1, Continue x2) {
        doDefaultAction(x1, x2);
    }

    @Override
    public void visit(CopyAssignment x1, CopyAssignment x2) {
        doDefaultAction(x1, x2);
    }

    @Override
    public void visit(Default x1, Default x2) {
        doDefaultAction(x1, x2);
    }

    @Override
    public void visit(Divide x1, Divide x2) {
        doDefaultAction(x1, x2);
    }

    @Override
    public void visit(DivideAssignment x1, DivideAssignment x2) {
        doDefaultAction(x1, x2);
    }

    @Override
    public void visit(Do x1, Do x2) {
        doDefaultAction(x1, x2);
    }

    @Override
    public void visit(DoubleLiteral x1, DoubleLiteral x2) {
        doDefaultAction(x1, x2);
    }

    @Override
    public void visit(Else x1, Else x2) {
        doDefaultAction(x1, x2);
    }

    @Override
    public void visit(EmptyStatement x1, EmptyStatement x2) {
        doDefaultAction(x1, x2);
    }

    @Override
    public void visit(Equals x1, Equals x2) {
        doDefaultAction(x1, x2);
    }

    @Override
    public void visit(ExactInstanceof x1, ExactInstanceof x2) {
        doDefaultAction(x1, x2);
    }

    @Override
    public void visit(ExecutionContext x1, ExecutionContext x2) {
        doDefaultAction(x1, x2);
    }

    @Override
    public void visit(Extends x1, Extends x2) {
        doDefaultAction(x1, x2);
    }

    @Override
    public void visit(EnhancedFor x1, EnhancedFor x2) {
        doDefaultAction(x1, x2);
    }

    @Override
    public void visit(FieldDeclaration x1, FieldDeclaration x2) {
        doDefaultAction(x1, x2);
    }

    @Override
    public void visit(FieldReference x1, FieldReference x2) {
        doDefaultAction(x1, x2);
    }

    @Override
    public void visit(FieldSpecification x1, FieldSpecification x2) {
        doDefaultAction(x1, x2);
    }

    @Override
    public void visit(Finally x1, Finally x2) {
        doDefaultAction(x1, x2);
    }

    @Override
    public void visit(FloatLiteral x1, FloatLiteral x2) {
        doDefaultAction(x1, x2);
    }

    @Override
    public void visit(For x1, For x2) {
        doDefaultAction(x1, x2);
    }

    @Override
    public void visit(ForUpdates x1, ForUpdates x2) {
        doDefaultAction(x1, x2);
    }

    @Override
    public void visit(GreaterOrEquals x1, GreaterOrEquals x2) {
        doDefaultAction(x1, x2);
    }

    @Override
    public void visit(GreaterThan x1, GreaterThan x2) {
        doDefaultAction(x1, x2);
    }

    @Override
    public void visit(Guard x1, Guard x2) {
        doDefaultAction(x1, x2);
    }

    @Override
    public void visit(If x1, If x2) {
        doDefaultAction(x1, x2);
    }

    @Override
    public void visit(Implements x1, Implements x2) {
        doDefaultAction(x1, x2);
    }

    @Override
    public void visit(ImplicitFieldSpecification x1, ImplicitFieldSpecification x2) {
        doDefaultAction(x1, x2);
    }

    @Override
    public void visit(Import x1, Import x2) {
        doDefaultAction(x1, x2);
    }

    @Override
    public void visit(Instanceof x1, Instanceof x2) {
        doDefaultAction(x1, x2);
    }

    @Override
    public void visit(InterfaceDeclaration x1, InterfaceDeclaration x2) {
        doDefaultAction(x1, x2);
    }

    @Override
    public void visit(IntLiteral x1, IntLiteral x2) {
        doDefaultAction(x1, x2);
    }

    @Override
    public void visit(LabeledStatement x1, LabeledStatement x2) {
        doDefaultAction(x1, x2);
    }

    @Override
    public void visit(LessOrEquals x1, LessOrEquals x2) {
        doDefaultAction(x1, x2);
    }

    @Override
    public void visit(LessThan x1, LessThan x2) {
        doDefaultAction(x1, x2);
    }

    @Override
    public void visit(LocalVariableDeclaration x1, LocalVariableDeclaration x2) {
        doDefaultAction(x1, x2);
    }

    @Override
    public void visit(LocationVariable x1, LocationVariable x2) {
        doDefaultAction(x1, x2);
    }

    @Override
    public void visit(LogicalAnd x1, LogicalAnd x2) {
        doDefaultAction(x1, x2);
    }

    @Override
    public void visit(LogicalNot x1, LogicalNot x2) {
        doDefaultAction(x1, x2);
    }

    @Override
    public void visit(LogicalOr x1, LogicalOr x2) {
        doDefaultAction(x1, x2);
    }

    @Override
    public void visit(LongLiteral x1, LongLiteral x2) {
        doDefaultAction(x1, x2);
    }

    @Override
    public void visit(LoopInit x1, LoopInit x2) {
        doDefaultAction(x1, x2);
    }

    @Override
    public void visit(MetaClassReference x1, MetaClassReference x2) {
        doDefaultAction(x1, x2);
    }

    @Override
    public void visit(MethodBodyStatement x1, MethodBodyStatement x2) {
        doDefaultAction(x1, x2);
    }

    @Override
    public void visit(MethodDeclaration x1, MethodDeclaration x2) {
        doDefaultAction(x1, x2);
    }

    @Override
    public void visit(MethodFrame x1, MethodFrame x2) {
        doDefaultAction(x1, x2);
    }

    @Override
    public void visit(MethodReference x1, MethodReference x2) {
        doDefaultAction(x1, x2);
    }

    @Override
    public void visit(Minus x1, Minus x2) {
        doDefaultAction(x1, x2);
    }

    @Override
    public void visit(MinusAssignment x1, MinusAssignment x2) {
        doDefaultAction(x1, x2);
    }

    @Override
    public void visit(Modifier x1, Modifier x2) {
        doDefaultAction(x1, x2);
    }

    @Override
    public void visit(Modulo x1, Modulo x2) {
        doDefaultAction(x1, x2);
    }

    @Override
    public void visit(ModuloAssignment x1, ModuloAssignment x2) {
        doDefaultAction(x1, x2);
    }

    @Override
    public void visit(Negative x1, Negative x2) {
        doDefaultAction(x1, x2);
    }

    @Override
    public void visit(New x1, New x2) {
        doDefaultAction(x1, x2);
    }

    @Override
    public void visit(NewArray x1, NewArray x2) {
        doDefaultAction(x1, x2);
    }

    @Override
    public void visit(NotEquals x1, NotEquals x2) {
        doDefaultAction(x1, x2);
    }

    @Override
    public void visit(NullLiteral x1, NullLiteral x2) {
        doDefaultAction(x1, x2);
    }

    @Override
    public void visit(PackageReference x1, PackageReference x2) {
        doDefaultAction(x1, x2);
    }

    @Override
    public void visit(PackageSpecification x1, PackageSpecification x2) {
        doDefaultAction(x1, x2);
    }

    @Override
    public void visit(ParameterDeclaration x1, ParameterDeclaration x2) {
        doDefaultAction(x1, x2);
    }

    @Override
    public void visit(ParenthesizedExpression x1, ParenthesizedExpression x2) {
        doDefaultAction(x1, x2);
    }

    @Override
    public void visit(PassiveExpression x1, PassiveExpression x2) {
        doDefaultAction(x1, x2);
    }

    @Override
    public void visit(Plus x1, Plus x2) {
        doDefaultAction(x1, x2);
    }

    @Override
    public void visit(PlusAssignment x1, PlusAssignment x2) {
        doDefaultAction(x1, x2);
    }

    @Override
    public void visit(Positive x1, Positive x2) {
        doDefaultAction(x1, x2);
    }

    @Override
    public void visit(PostDecrement x1, PostDecrement x2) {
        doDefaultAction(x1, x2);
    }

    @Override
    public void visit(PostIncrement x1, PostIncrement x2) {
        doDefaultAction(x1, x2);
    }

    @Override
    public void visit(PreDecrement x1, PreDecrement x2) {
        doDefaultAction(x1, x2);
    }

    @Override
    public void visit(PreIncrement x1, PreIncrement x2) {
        doDefaultAction(x1, x2);
    }

    @Override
    public void visit(ProgramConstant x1, ProgramConstant x2) {
        doDefaultAction(x1, x2);
    }

    @Override
    public void visit(ProgramElementName x1, ProgramElementName x2) {
        doDefaultAction(x1, x2);
    }

    @Override
    public void visit(ProgramTransformer x1, ProgramTransformer x2) {
        doDefaultAction(x1, x2);
    }

    @Override
    public void visit(ProgramMethod x1, ProgramMethod x2) {
        doDefaultAction(x1, x2);
    }

    @Override
    public void visit(ProgramVariable x1, ProgramVariable x2) {
        doDefaultAction(x1, x2);
    }

    @Override
    public void visit(IProgramVariable x1, IProgramVariable x2) {
        doDefaultAction(x1, x2);
    }

    @Override
    public void visit(Return x1, Return x2) {
        doDefaultAction(x1, x2);
    }

    @Override
    public void visit(SchematicFieldReference x1, SchematicFieldReference x2) {
        doDefaultAction(x1, x2);
    }

    @Override
    public void visit(SchemaVariable x1, SchemaVariable x2) {
        doDefaultAction((ProgramSV) x1, (ProgramSV) x2);
    }

    @Override
    public void visit(ShiftLeft x1, ShiftLeft x2) {
        doDefaultAction(x1, x2);
    }

    @Override
    public void visit(ShiftLeftAssignment x1, ShiftLeftAssignment x2) {
        doDefaultAction(x1, x2);
    }

    @Override
    public void visit(ShiftRight x1, ShiftRight x2) {
        doDefaultAction(x1, x2);
    }

    @Override
    public void visit(ShiftRightAssignment x1, ShiftRightAssignment x2) {
        doDefaultAction(x1, x2);
    }

    @Override
    public void visit(StatementBlock x1, StatementBlock x2) {
        doDefaultAction(x1, x2);
    }

    @Override
    public void visit(StringLiteral x1, StringLiteral x2) {
        doDefaultAction(x1, x2);
    }

    @Override
    public void visit(SuperArrayDeclaration x1, SuperArrayDeclaration x2) {
        doDefaultAction(x1, x2);
    }

    @Override
    public void visit(SuperConstructorReference x1, SuperConstructorReference x2) {
        doDefaultAction(x1, x2);
    }

    @Override
    public void visit(SuperReference x1, SuperReference x2) {
        doDefaultAction(x1, x2);
    }

    @Override
    public void visit(Switch x1, Switch x2) {
        doDefaultAction(x1, x2);
    }

    @Override
    public void visit(SynchronizedBlock x1, SynchronizedBlock x2) {
        doDefaultAction(x1, x2);
    }

    @Override
    public void visit(Then x1, Then x2) {
        doDefaultAction(x1, x2);
    }

    @Override
    public void visit(ThisConstructorReference x1, ThisConstructorReference x2) {
        doDefaultAction(x1, x2);
    }

    @Override
    public void visit(ThisReference x1, ThisReference x2) {
        doDefaultAction(x1, x2);
    }

    @Override
    public void visit(Throw x1, Throw x2) {
        doDefaultAction(x1, x2);
    }

    @Override
    public void visit(Throws x1, Throws x2) {
        doDefaultAction(x1, x2);
    }

    @Override
    public void visit(Times x1, Times x2) {
        doDefaultAction(x1, x2);
    }

    @Override
    public void visit(TimesAssignment x1, TimesAssignment x2) {
        doDefaultAction(x1, x2);
    }

    @Override
    public void visit(Try x1, Try x2) {
        doDefaultAction(x1, x2);
    }

    @Override
    public void visit(TypeCast x1, TypeCast x2) {
        doDefaultAction(x1, x2);
    }

    @Override
    public void visit(TypeRef x1, TypeRef x2) {
        doDefaultAction(x1, x2);
    }

    @Override
    public void visit(UnsignedShiftRight x1, UnsignedShiftRight x2) {
        doDefaultAction(x1, x2);
    }

    @Override
    public void visit(UnsignedShiftRightAssignment x1,
            UnsignedShiftRightAssignment x2) {
        doDefaultAction(x1, x2);
    }

    @Override
    public void visit(VariableDeclaration x1, VariableDeclaration x2) {
        doDefaultAction(x1, x2);
    }

    @Override
    public void visit(VariableReference x1, VariableReference x2) {
        doDefaultAction(x1, x2);
    }

    @Override
    public void visit(VariableSpecification x1, VariableSpecification x2) {
        doDefaultAction(x1, x2);
    }

    @Override
    public void visit(While x1, While x2) {
        doDefaultAction(x1, x2);
    }

    @Override
    public void visit(LoopInvariant x) {
        // do nothing
    }

    @Override
    public void visit(BlockContract x) {
        // do nothing
    }

    @Override
    public void visit(TransactionStatement x1, TransactionStatement x2) {
        doDefaultAction(x1, x2);
    }

    @Override
    public void visit(EmptyMapLiteral x1, EmptyMapLiteral x2) {
        doDefaultAction(x1, x2);
    }

}
