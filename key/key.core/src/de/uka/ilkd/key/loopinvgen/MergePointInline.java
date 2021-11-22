package de.uka.ilkd.key.loopinvgen;


import java.io.File;
import java.io.PrintWriter;
import java.io.StringWriter;
import java.util.LinkedList;
import java.util.List;

import org.antlr.runtime.RecognitionException;
import org.key_project.util.ExtList;
import org.key_project.util.collection.ImmutableSLList;

import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Recoder2KeY;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.Statement;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.PrimitiveType;
import de.uka.ilkd.key.java.statement.EmptyStatement;
import de.uka.ilkd.key.java.statement.MergePointStatement;
import de.uka.ilkd.key.java.visitor.CreatingASTVisitor;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.NamespaceSet;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.parser.KeYLexerF;
import de.uka.ilkd.key.parser.KeYParserF;
import de.uka.ilkd.key.parser.ParserConfig;
import de.uka.ilkd.key.parser.ParserMode;
import de.uka.ilkd.key.pp.AbbrevMap;
import de.uka.ilkd.key.proof.io.ProofSaver;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.merge.MergeProcedure;
import de.uka.ilkd.key.rule.merge.procedures.MergeByIfThenElse;
import de.uka.ilkd.key.rule.merge.procedures.MergeIfThenElseAntecedent;
import de.uka.ilkd.key.speclang.MergeContract;
import de.uka.ilkd.key.speclang.UnparameterizedMergeContract;

public class MergePointInline extends CreatingASTVisitor { 
	private final TermBuilder tb;
	private final NamespaceSet nss;
	private final Services services;
	private List<MergeContract> contracts = new LinkedList<>();
	public MergePointInline(ProgramElement root, boolean preservesPos, Services services) {
		super(root, preservesPos, services);
		this.services=services;
		tb = services.getTermBuilder();
		nss = services.getNamespaces();
	}
	
	public ProgramElement inline()
    {
        stack.push(new ExtList());
        walk(root());
        ExtList el = stack.peek();
        return el.get(ProgramElement.class);
    }

    public List<MergeContract> getContracts() {
		return contracts;
	}

	protected void doAction(ProgramElement element)
    {
        if (element instanceof EmptyStatement) {
        	final KeYJavaType mergePointIndexType = services.getJavaInfo().getKeYJavaType(PrimitiveType.JAVA_INT);
			LocationVariable newIndexVar = new LocationVariable(new ProgramElementName(tb.newName("#mpIndex", nss)), 
        			mergePointIndexType);	            
        	final MergePointStatement mergePoint = new MergePointStatement(newIndexVar);
			final MergeProcedure mergeProcedure = new MergeByIfThenElse();//new MergeIfThenElseAntecedent();
        	final MergeContract mergeContract = new UnparameterizedMergeContract(mergeProcedure, 
					mergePoint, mergePointIndexType);
        	this.contracts.add(mergeContract);
        	addChild(mergePoint);
            changed();
        }
        else {
            super.doAction(element);
        }
    }
	}