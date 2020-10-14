/*
 * Created on 31.03.2006
 *
 * This file is part of the RECODER library and protected by the LGPL.
 * 
 */
package recoder.kit.transformation.java5to4;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import recoder.CrossReferenceServiceConfiguration;
import recoder.ParserException;
import recoder.ProgramFactory;
import recoder.abstraction.Type;
import recoder.convenience.TreeWalker;
import recoder.java.CompilationUnit;
import recoder.java.Expression;
import recoder.java.LoopInitializer;
import recoder.java.ProgramElement;
import recoder.java.Statement;
import recoder.java.StatementBlock;
import recoder.java.declaration.AnnotationUseSpecification;
import recoder.java.declaration.ClassDeclaration;
import recoder.java.declaration.ConstructorDeclaration;
import recoder.java.declaration.DeclarationSpecifier;
import recoder.java.declaration.EnumConstantDeclaration;
import recoder.java.declaration.EnumConstantSpecification;
import recoder.java.declaration.EnumDeclaration;
import recoder.java.declaration.FieldDeclaration;
import recoder.java.declaration.FieldSpecification;
import recoder.java.declaration.Implements;
import recoder.java.declaration.LocalVariableDeclaration;
import recoder.java.declaration.MemberDeclaration;
import recoder.java.declaration.MethodDeclaration;
import recoder.java.declaration.ParameterDeclaration;
import recoder.java.declaration.VariableSpecification;
import recoder.java.declaration.modifier.Static;
import recoder.java.expression.ParenthesizedExpression;
import recoder.java.expression.operator.CopyAssignment;
import recoder.java.expression.operator.New;
import recoder.java.expression.operator.NewArray;
import recoder.java.reference.ArrayReference;
import recoder.java.reference.FieldReference;
import recoder.java.reference.MethodReference;
import recoder.java.reference.ReferencePrefix;
import recoder.java.reference.TypeReference;
import recoder.java.reference.VariableReference;
import recoder.java.statement.Branch;
import recoder.java.statement.Case;
import recoder.java.statement.Default;
import recoder.java.statement.For;
import recoder.java.statement.If;
import recoder.java.statement.Switch;
import recoder.kit.MiscKit;
import recoder.kit.ProblemReport;
import recoder.kit.TwoPassTransformation;
import recoder.kit.TypeKit;
import recoder.kit.UnitKit;
import recoder.kit.VariableKit;
import recoder.list.generic.ASTArrayList;
import recoder.list.generic.ASTList;

/**
 * untested for enum declarations nested within enum declarations
 * @author Tobias Gutzmann
 *
 */
public class ReplaceEnums extends TwoPassTransformation {

	

	public class ReplaceSingleEnum extends TwoPassTransformation {
		private EnumDeclaration ed;
		private String name;
		private ClassDeclaration repl;
		private Set<Switch> switchStmnts;
		private Map<Switch, String[]> names; 
		
		public ReplaceSingleEnum(CrossReferenceServiceConfiguration sc, EnumDeclaration ed) {
			super(sc);
			this.ed = ed;
		}
		
		@Override
		public ProblemReport analyze() {
			switchStmnts = new HashSet<Switch>();
			boolean constructor = false;
			names = new HashMap<Switch, String[]>();
			List<String[]> tempNames = new ArrayList<String[]>();
			ProgramFactory f = getProgramFactory();
			repl = f.createClassDeclaration();
			repl.setParent(ed.getParent());
			repl.setProgramModelInfo(ed.getProgramModelInfo());
			if (ed.getDeclarationSpecifiers() != null)
				repl.setDeclarationSpecifiers(ed.getDeclarationSpecifiers().deepClone());
			else 
				repl.setDeclarationSpecifiers(new ASTArrayList<DeclarationSpecifier>(1));
			if (ed.isFinal())
				repl.getDeclarationSpecifiers().add(f.createFinal());
//			make Declaration static otherwise it's an inner class and must not declare static members
			boolean isStatic = false;
			if (ed.getDeclarationSpecifiers() != null) {
				for (DeclarationSpecifier ds : ed.getDeclarationSpecifiers()) {
					if (Static.class.isInstance(ds)) {
						isStatic = true;
					}
				}
			}
			if (!isStatic && MiscKit.getParentTypeDeclaration(ed) != null)
				repl.getDeclarationSpecifiers().add(f.createStatic());
			if (ed.getComments() != null)
				repl.setComments(ed.getComments().deepClone());
			if (ed.getImplementedTypes() != null) {
				Implements impl = ed.getImplementedTypes();
				ASTList<TypeReference> types =  impl.getSupertypes();
				types.add(TypeKit.createTypeReference(f, "Comparable"));
				try {
					types.add(f.parseTypeReference("java.io.Serializable"));
				}
				catch(ParserException e) {
					System.err.println("parsing Exception");
				}
				impl = new Implements(types);
				impl.setParent(repl);
				repl.setImplementedTypes(impl);
				repl.makeParentRoleValid();
			}
			else {
				ASTList<TypeReference> types = new ASTArrayList<TypeReference>(2);
				types.add(TypeKit.createTypeReference(f, "Comparable"));
				try {
					types.add(f.parseTypeReference("java.io.Serializable"));
				}
				catch(ParserException e) {
					System.err.println("parsing Exception");
				}
				Implements impl = new Implements(types);
				impl.setParent(repl);
				repl.setImplementedTypes(impl);
				repl.makeParentRoleValid();
			}
			ASTArrayList<MemberDeclaration> mlist = new ASTArrayList<MemberDeclaration>(ed.getMembers().size());
			repl.setMembers(mlist);
			repl.setIdentifier(ed.getIdentifier().deepClone());
			name = VariableKit.createValidVariableName(getSourceInfo(), ed.getChildAt(0), "name");
			// if no constructors available add constructor with (String name)
			// available constructors are extended with Parameter String name later
//			if (ed.getConstructors() == null || ed.getConstructors().size() == 0) {
//				System.out.println("No Constructor");
//				ConstructorDeclaration cd = f.createConstructorDeclaration();
//				cd.setIdentifier(ed.getIdentifier().deepClone());
//				ASTList<Statement> block = new ASTArrayList<Statement>(1);
//				CopyAssignment ca = f.createCopyAssignment(
//						f.createVariableReference(f.createIdentifier("name")), 
//						f.createFieldReference(f.createIdentifier("name")));
//				block.add(ca);
//				StatementBlock body = f.createStatementBlock(block);
//				cd.setBody(body);
//				mlist.add(cd);
//			}
			
			boolean containsToString = false;
			for (MemberDeclaration md : ed.getMembers()) {
				if (md instanceof MethodDeclaration) {
					MethodDeclaration methDec = (MethodDeclaration)md;
					if (methDec.getName().equals("toString")) {
						containsToString = true;
						break;
					}
				}
			}
			
//			needed later for valueOf() and values()
			ASTArrayList<FieldSpecification> enumSpecRepl = new ASTArrayList<FieldSpecification>(); 
			int constants = 0;
			for (int i = 0; i < ed.getMembers().size(); i++) {
				MemberDeclaration md = ed.getMembers().get(i);
				if (md instanceof EnumConstantDeclaration) {
					EnumConstantDeclaration ec = (EnumConstantDeclaration)md;
					EnumConstantSpecification ecs = ec.getEnumConstantSpecification();

					// create replacement for current constant
					ASTArrayList<DeclarationSpecifier> dsml = new ASTArrayList<DeclarationSpecifier>();
					if (ec.getAnnotations() != null) {
						for (AnnotationUseSpecification a : ec.getAnnotations()) {
							dsml.add(a.deepClone());
						}
					}
					dsml.add(f.createFinal());
					dsml.add(f.createPublic());
					dsml.add(f.createStatic());
					FieldDeclaration enumConst = f.createFieldDeclaration(dsml.deepClone(),
							TypeKit.createTypeReference(f, "int"),
							f.createIdentifier("ENUMCONST_" + ecs.getIdentifier().getText()),
							null);
					FieldSpecification fSpec = enumConst.getFieldSpecifications().get(0);
					fSpec.setInitializer(f.createIntLiteral(constants));
					constants++;
					fSpec.makeParentRoleValid();
					enumConst.makeParentRoleValid();
					mlist.add(enumConst);
					
					FieldDeclaration fd = f.createFieldDeclaration(
							dsml,
							f.createTypeReference(ed.getIdentifier().deepClone()),
							ecs.getIdentifier().deepClone(),
							null
						);
					FieldSpecification fs = fd.getFieldSpecifications().get(0);
					
//					update references: parent instanceof Switch ?
					List<FieldReference> frl = getCrossReferenceSourceInfo().getReferences(ecs);
					for (int j = 0; j < frl.size(); j++) {
						FieldReference fr = frl.get(j);
						if (fr.getASTParent() instanceof Case && ((Case)fr.getASTParent()).getExpression().equals(fr)) {
//							System.out.println("Switch Statement");
							Switch sw = (Switch)fr.getASTParent().getASTParent();
							//TOCO fallThrough und doneAny und demensprechend auch names wird nicht mehr verwendet
							String fallThroughName = VariableKit.createValidVariableName(
									getSourceInfo(),
									sw,
									"fallThrough"
							);
							String doneAnyName = VariableKit.createValidVariableName(
									getSourceInfo(),
									sw,
									"doneAny"
							);
							if (getSourceInfo().getContainingClassType(sw).equals(ed)) {
								tempNames.add(new String[] {fallThroughName, doneAnyName});
							}
							else {
								switchStmnts.add(sw);
								names.put(sw, new String[] { fallThroughName, doneAnyName});
							}
						}
					}
					
					New e = f.createNew();
					e.setTypeReference(f.createTypeReference(repl.getIdentifier()));
					ASTArrayList<Expression> args = null;
					if (ecs.getConstructorReference().getArguments() != null || ecs.getConstructorReference().getClassDeclaration() != null) {
						List<Expression> ecsargs = ecs.getConstructorReference().getArguments();
						int s = ecsargs == null ? 0 : ecsargs.size();
						args = new ASTArrayList<Expression>(s);
						for (int j = 0; j < s; j++)
							args.add(ecsargs.get(j).deepClone());
						if (ecs.getConstructorReference().getClassDeclaration() != null) {
							e.setClassDeclaration(ecs.getConstructorReference().getClassDeclaration().deepClone());
						}
					}
					if (args == null) {
						args = new ASTArrayList<Expression>(1);
					}
					args.add(f.createStringLiteral("\"" + ecs.getIdentifier().getText() + "\""));
					e.setArguments(args);
					fs.setInitializer(e);
					e.makeParentRoleValid();
					fs.makeParentRoleValid();
					fd.makeParentRoleValid();
					enumSpecRepl.add(fs);
					mlist.add(fd);
				} else if (md instanceof ConstructorDeclaration) {
					ConstructorDeclaration cd = (ConstructorDeclaration)md;
					ParameterDeclaration pd = f.createParameterDeclaration(f.createTypeReference(f.createIdentifier("String")), f.createIdentifier(name));
					cd.getParameters().add(pd);
					
					FieldReference fr = f.createFieldReference();
					fr.setReferencePrefix(f.createThisReference());
					fr.setIdentifier(f.createIdentifier(name));
					cd.getBody().getBody().add(f.createCopyAssignment(
							fr, 
							f.createVariableReference(f.createIdentifier(name))));
					mlist.add((MemberDeclaration)md.deepClone());
					cd.makeAllParentRolesValid();
					constructor = true;
				} else {
					if (md instanceof MethodDeclaration) {
						MethodDeclaration methDecl = (MethodDeclaration)md.deepClone();
						if (methDecl.isAbstract() && !repl.isAbstract()) {
							repl.getDeclarationSpecifiers().add(f.createAbstract());
						}
					}
					MemberDeclaration memDecl = (MemberDeclaration)md.deepClone();
					memDecl.setMemberParent(repl);
					mlist.add(memDecl);
				
				}
			}
			if (!constructor) {
				ConstructorDeclaration cd = f.createConstructorDeclaration();
				cd.setIdentifier(ed.getIdentifier().deepClone());
				ASTList<ParameterDeclaration> list = new ASTArrayList<ParameterDeclaration>(1);
				list.add(f.createParameterDeclaration(f.createTypeReference(f.createIdentifier("String")), f.createIdentifier(name)));
				cd.setParameters(list);
				ASTList<Statement> block = new ASTArrayList<Statement>(1);
				FieldReference fr = f.createFieldReference();
				fr.setReferencePrefix(f.createThisReference());
				fr.setIdentifier(f.createIdentifier(name));
				CopyAssignment ca = f.createCopyAssignment(
						fr, 
						f.createVariableReference(f.createIdentifier(name)));
				block.add(ca);
				StatementBlock body = f.createStatementBlock(block);
				cd.setBody(body);
				mlist.add(cd);
				cd.makeAllParentRolesValid();
			}
			//check for internal switch statement in the now cloned EnumDeclaration otherwise references
			//internal switch statements will point to the later replaced AST part
			TreeWalker tw = new TreeWalker(repl);
			while (tw.next()) {
				ProgramElement pe = tw.getProgramElement();
				if (pe instanceof Switch) {
					Switch sw = (Switch)pe;
					System.out.println(UnitKit.getCompilationUnit(ed).getName());
					Type t;
					if (sw.getExpression() instanceof VariableReference) {
						VariableSpecification vs = (VariableSpecification)getSourceInfo().getVariable((VariableReference)sw.getExpression());
						vs.setProgramModelInfo(getSourceInfo());
						t = getSourceInfo().getType(vs);
					}
					else {
						t = getSourceInfo().getType(sw.getExpression());
					}
					if (t != null && t.getName().equals(ed.getName())) {
						System.out.println("tuut");
						switchStmnts.add(sw);
						if (tempNames.size() > 0)
							names.put(sw, tempNames.remove(0));
					}
				}
			}
			
			// now add values(), valueOf(), toString(), name(), hashCode(), equals(), compareTo(),
			// getDeclaringClass() and ordinal()
			MethodDeclaration values = f.createMethodDeclaration();
			MethodDeclaration valueOf = f.createMethodDeclaration();
			MethodDeclaration ordinal = f.createMethodDeclaration();
			MethodDeclaration toString = f.createMethodDeclaration();
			MethodDeclaration nameM = f.createMethodDeclaration();
			MethodDeclaration hashCode = f.createMethodDeclaration();
			MethodDeclaration equals = f.createMethodDeclaration();
			MethodDeclaration compareTo = f.createMethodDeclaration();
			MethodDeclaration getDeclaringClass = f.createMethodDeclaration();
			values.setIdentifier(f.createIdentifier("values"));
			valueOf.setIdentifier(f.createIdentifier("valueOf"));
			ordinal.setIdentifier(f.createIdentifier("ordinal"));
			toString.setIdentifier(f.createIdentifier("toString"));
			nameM.setIdentifier(f.createIdentifier("name"));
			hashCode.setIdentifier(f.createIdentifier("hashCode"));
			equals.setIdentifier(f.createIdentifier("equals"));
			compareTo.setIdentifier(f.createIdentifier("compareTo"));
			getDeclaringClass.setIdentifier(f.createIdentifier("getDeclaringClass"));
			ASTArrayList<DeclarationSpecifier> declSpecs = new ASTArrayList<DeclarationSpecifier>();
			declSpecs.add(f.createPrivate());
			declSpecs.add(f.createFinal());
			FieldDeclaration nameFD = f.createFieldDeclaration(f.createTypeReference(f.createIdentifier("String")),
					f.createIdentifier(name));
			nameFD.setDeclarationSpecifiers(declSpecs);
			nameFD.makeParentRoleValid();
			mlist.add(nameFD);
			declSpecs = new ASTArrayList<DeclarationSpecifier>();
			declSpecs.add(f.createPublic());
			toString.setDeclarationSpecifiers(declSpecs.deepClone());
			nameM.setDeclarationSpecifiers(declSpecs.deepClone());
			hashCode.setDeclarationSpecifiers(declSpecs.deepClone());
			equals.setDeclarationSpecifiers(declSpecs.deepClone());
			compareTo.setDeclarationSpecifiers(declSpecs.deepClone());
			getDeclaringClass.setDeclarationSpecifiers(declSpecs.deepClone());
			declSpecs.add(f.createStatic());
			values.setDeclarationSpecifiers(declSpecs);
			values.makeParentRoleValid();
			// clone for valueOf()
			declSpecs = declSpecs.deepClone();
			valueOf.setDeclarationSpecifiers(declSpecs);
			// clone/change for ordinal()
			declSpecs = declSpecs.deepClone();
			declSpecs.remove(1);
			declSpecs.add(f.createFinal());
			ordinal.setDeclarationSpecifiers(declSpecs);
			ordinal.makeParentRoleValid();
			values.setTypeReference(f.createTypeReference(repl.getIdentifier().deepClone(), 1));
			valueOf.setTypeReference(f.createTypeReference(repl.getIdentifier().deepClone()));
			ordinal.setTypeReference(f.createTypeReference(f.createIdentifier("int")));
			toString.setTypeReference(f.createTypeReference(f.createIdentifier("String")));
			nameM.setTypeReference(f.createTypeReference(f.createIdentifier("String")));
			hashCode.setTypeReference(f.createTypeReference(f.createIdentifier("int")));
			equals.setTypeReference(f.createTypeReference(f.createIdentifier("boolean")));
			compareTo.setTypeReference(f.createTypeReference(f.createIdentifier("int")));
			getDeclaringClass.setTypeReference(TypeKit.createTypeReference(f, "Class"));
			valueOf.setParameters(
					new ASTArrayList<ParameterDeclaration>(
							f.createParameterDeclaration(TypeKit.createTypeReference(f, "String"),
							f.createIdentifier("name")		
							)
					)
			);
			equals.setParameters(
					new ASTArrayList<ParameterDeclaration>(
							f.createParameterDeclaration(TypeKit.createTypeReference(f, "Object"),
							f.createIdentifier("other")
							)
					)
			);
			compareTo.setParameters(
					new ASTArrayList<ParameterDeclaration>(
//							f.createParameterDeclaration(f.createTypeReference(ed.getIdentifier().deepClone()),
							f.createParameterDeclaration(f.createTypeReference(f.createIdentifier("Object")),
							f.createIdentifier("o")
							)
					)
			);
			// now, add functional behaviour
			StatementBlock valuesSt = f.createStatementBlock();
			StatementBlock valueOfSt = f.createStatementBlock();
			StatementBlock ordinalSt = f.createStatementBlock();
			StatementBlock toStringSt = f.createStatementBlock();
			StatementBlock nameMSt = f.createStatementBlock();
			StatementBlock hashCodeSt = f.createStatementBlock();
			StatementBlock equalsSt = f.createStatementBlock();
			StatementBlock compareToSt = f.createStatementBlock();
			StatementBlock getDeclaringClassSt = f.createStatementBlock();
			values.setBody(valuesSt);
			valueOf.setBody(valueOfSt);
			ordinal.setBody(ordinalSt);
			toString.setBody(toStringSt);
			nameM.setBody(nameMSt);
			hashCode.setBody(hashCodeSt);
			equals.setBody(equalsSt);
			compareTo.setBody(compareToSt);
			getDeclaringClass.setBody(getDeclaringClassSt);
			
			// ordinal and toString first
			ordinalSt.setBody(new ASTArrayList<Statement>(f.createReturn(f.createFieldReference(f.createIdentifier("ordinal")))));
			hashCodeSt.setBody(new ASTArrayList<Statement>(f.createReturn(f.createFieldReference(f.createIdentifier("ordinal")))));
			toStringSt.setBody(new ASTArrayList<Statement>(f.createReturn(f.createFieldReference(f.createIdentifier(name)))));
			nameMSt.setBody(new ASTArrayList<Statement>(f.createReturn(f.createFieldReference(f.createIdentifier(name)))));
			equalsSt.setBody(new ASTArrayList<Statement>(f.createReturn(f.createEquals(f.createThisReference(), f.createVariableReference(f.createIdentifier("other"))))));
			ParenthesizedExpression pExpr = f.createParenthesizedExpression(
					f.createTypeCast(f.createVariableReference(f.createIdentifier("o")), f.createTypeReference(ed.getIdentifier().deepClone())));
			FieldReference fRef = f.createFieldReference(f.createIdentifier("ordinal"));
			pExpr.setReferenceSuffix(fRef);
			fRef.setReferencePrefix(pExpr);
			pExpr.makeParentRoleValid();
			fRef.makeParentRoleValid();
			compareToSt.setBody(new ASTArrayList<Statement>(
					f.createReturn(
							f.createMinus(
									f.createFieldReference(f.createIdentifier("ordinal")),
									fRef.deepClone()
									)
							)
					)
			);
			getDeclaringClassSt.setBody(new ASTArrayList<Statement>(
					f.createReturn(f.createMetaClassReference(f.createTypeReference(ed.getIdentifier())))
			));
			
			// na must be filled for values, ite iteratively extended
			NewArray na = f.createNewArray();
			na.setTypeReference(f.createTypeReference(repl.getIdentifier().deepClone(),1));
			na.setArrayInitializer(f.createArrayInitializer(new ASTArrayList<Expression>(enumSpecRepl.size())));
			na.makeParentRoleValid();
			valuesSt.setBody(new ASTArrayList<Statement>(f.createReturn(na)));
			// TODO doesn't work if no enum constants are declared (makes no sense, but yet...)
			ASTList<Statement> stmtList = new ASTArrayList<Statement>();
			valueOfSt.setBody(stmtList);
			If ite = f.createIf();
			LocalVariableDeclaration lvd = new LocalVariableDeclaration(null, TypeKit.createTypeReference(f, "int"), f.createIdentifier("i"), f.createIntLiteral(0));
			FieldReference fieldRef = f.createFieldReference(f.createIdentifier("length"));
			MethodReference methRef = f.createMethodReference(f.createIdentifier("values"));
			fieldRef.setReferencePrefix(methRef.deepClone());
			fieldRef.makeAllParentRolesValid();
			For fst = f.createFor(new ASTArrayList<LoopInitializer>(lvd),
					f.createLessThan(f.createVariableReference(f.createIdentifier("i")), fieldRef.deepClone()), 
					new ASTArrayList<Expression>(f.createPostIncrement(f.createVariableReference(f.createIdentifier("i")))),
					ite);
			methRef = f.createMethodReference(f.createIdentifier("values"));
			ArrayReference arrRef = f.createArrayReference(methRef, new ASTArrayList<Expression>(f.createVariableReference(f.createIdentifier("i"))));
			arrRef.setReferencePrefix(methRef.deepClone());
			arrRef.makeParentRoleValid();
			ArrayReference arrRef2 = arrRef.deepClone();
			methRef = f.createMethodReference(f.createIdentifier("name"));
			methRef.setReferencePrefix(arrRef.deepClone());
			methRef.makeParentRoleValid();
			MethodReference methRef2 = f.createMethodReference(f.createIdentifier("equals"), new ASTArrayList<Expression>(f.createVariableReference(f.createIdentifier("name"))));
			methRef2.setReferencePrefix(methRef.deepClone());
			methRef2.makeParentRoleValid();
			ite.setExpression(methRef2.deepClone());
			ite.setThen(f.createThen(f.createReturn(arrRef2)));
			ite.makeParentRoleValid();
			stmtList.add(fst);
			stmtList.add(f.createThrow(f.createNew(null,f.createTypeReference(f.createIdentifier("IllegalArgumentException")),null)));
			fst.makeParentRoleValid();
			for (int i = 0; i < enumSpecRepl.size(); i++) {
				FieldSpecification fs = enumSpecRepl.get(i);
				na.getArrayInitializer().getArguments().add(f.createFieldReference(fs.getIdentifier().deepClone()));
//				ite.setExpression(
//						f.createMethodReference(
//								f.createVariableReference(f.createIdentifier("name")),
//								f.createIdentifier("equals"),
//								new ASTArrayList<Expression>(
//										f.createStringLiteral("\"" + fs.getName() + "\"")
//								)
//								
//						)
//				);
//				ite.setThen(f.createThen(f.createReturn(f.createFieldReference(fs.getIdentifier().deepClone()))));
//				if (i+1 < enumSpecRepl.size()) { 
//					ite.setElse(f.createElse(f.createIf()));
//					ite.makeParentRoleValid();
//					ite = (If)ite.getElse().getStatementAt(0);
//				} else {
//					ite.makeParentRoleValid();
//				}
			}
			na.getArrayInitializer().makeParentRoleValid();
//			ite.setElse(f.createElse(f.createThrow(f.createNew(null,f.createTypeReference(f.createIdentifier("IllegalArgumentException")),null))));
//			ite.makeParentRoleValid();
			valuesSt.makeParentRoleValid();
			valueOfSt.makeParentRoleValid();
			ordinalSt.makeParentRoleValid();
			toStringSt.makeParentRoleValid();
			nameMSt.makeParentRoleValid();
			hashCodeSt.makeParentRoleValid();
			equalsSt.makeParentRoleValid();
			compareToSt.makeParentRoleValid();
			getDeclaringClassSt.makeParentRoleValid();
			
			valueOf.makeParentRoleValid();
			values.makeParentRoleValid();
			ordinal.makeParentRoleValid();
			toString.makeParentRoleValid();
			nameM.makeParentRoleValid();
			hashCode.makeParentRoleValid();
			equals.makeParentRoleValid();
			compareTo.makeParentRoleValid();
			getDeclaringClass.makeParentRoleValid();
			mlist.add(valueOf);
			mlist.add(values);
			mlist.add(ordinal);
			if (!containsToString) mlist.add(toString);
			mlist.add(nameM);
			mlist.add(hashCode);
			mlist.add(equals);
			mlist.add(compareTo);
			mlist.add(getDeclaringClass);

			// also add fields for ordinal 
			declSpecs = new ASTArrayList<DeclarationSpecifier>(2);
			declSpecs.add(f.createPrivate());
			declSpecs.add(f.createStatic());
			mlist.add(f.createFieldDeclaration(declSpecs,
					f.createTypeReference(f.createIdentifier("int")),
					f.createIdentifier("CURRENT_ORDINAL"), 
					f.createIntLiteral("0"))
			);
			declSpecs = new ASTArrayList<DeclarationSpecifier>(2);
			declSpecs.add(f.createPrivate());
			declSpecs.add(f.createFinal());
			mlist.add(f.createFieldDeclaration(declSpecs, 
					f.createTypeReference(f.createIdentifier("int")), 
					f.createIdentifier("ordinal"), 
					f.createPostIncrement(f.createFieldReference(f.createIdentifier("CURRENT_ORDINAL"))))
			);
			// done
			repl.makeParentRoleValid();
			MiscKit.unindent(repl);
			return super.analyze();
		}

		@Override
		public void transform() {
//			super.transform();
			for (Switch sw : switchStmnts) {
				ProgramFactory f = getProgramFactory();
				Switch newSwitch = sw.deepClone();
				Expression cond = newSwitch.getExpression().deepClone();
				cond = new MethodReference((ReferencePrefix)cond, f.createIdentifier("ordinal"));
				newSwitch.setExpression(cond.deepClone());
				ASTList<Branch> branches = new ASTArrayList<Branch>();
				for (int i = 0; i < newSwitch.getBranchCount(); i++) {
					Branch b = newSwitch.getBranchAt(i);
					if (b instanceof Case) {
						Case c = (Case)b;
						cond = c.getExpression().deepClone();
						cond = new FieldReference(TypeKit.createTypeReference(f, ed.getFullName()), f.createIdentifier("ENUMCONST_" + ((FieldReference)cond).getName()));
						c.setExpression(cond);
						branches.add(c.deepClone());
					}
					else if (b instanceof Default) {
						branches.add(b);
					}
				}
				newSwitch.setBranchList(branches);
				newSwitch.makeAllParentRolesValid();
				replace(sw, newSwitch);
			}
			replace(ed, repl);
		}
	}

	private List<CompilationUnit> cul;
	private List<ReplaceSingleEnum> parts;
	
	/**
	 * 
	 */
	public ReplaceEnums(CrossReferenceServiceConfiguration sc, CompilationUnit cu) {
		super(sc);
		cul = new ArrayList<CompilationUnit>();
		cul.add(cu);
	}
	
	public ReplaceEnums(CrossReferenceServiceConfiguration sc, List<CompilationUnit> cul) {
		super(sc);
		this.cul = cul;
	}

	@Override
	public ProblemReport analyze() {
		parts = new ArrayList<ReplaceSingleEnum>();
		TreeWalker tw;
		for (CompilationUnit cu : cul) {
			tw = new TreeWalker(cu);
			while (tw.next()) {
				ProgramElement pe = tw.getProgramElement();
				if (pe instanceof EnumDeclaration) {
					ReplaceSingleEnum p = new ReplaceSingleEnum(getServiceConfiguration(), (EnumDeclaration)pe);
					p.analyze();
					parts.add(p);
				}
			}
		}
		
		return super.analyze();
	}

	@Override
	public void transform() {
		super.transform();
		System.out.println(parts.size() + " Enums to be transformed");
		for (int i = parts.size()-1; i >= 0; i--) {
			parts.get(i).transform();
		}
	}
}
