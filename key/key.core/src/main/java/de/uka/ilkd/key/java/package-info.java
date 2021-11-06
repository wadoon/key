/**
 * This package contains classes that cover the Java programming language.
 * <p>
 * The classes in the subpackages are mainly taken from the Recoder
 * framework and made immutable. They are transformed into this data
 * structure from a Recoder structure by {@link de.uka.ilkd.key.java.translation.Recoder2KeY}
 * or {@link de.uka.ilkd.key.java.translation.SchemaRecoder2KeY}. However, in some details both
 * data structures might differ more.
 * <p>
 * The following explanations are adapted from the
 * documentation of the Recoder framework.
 * <DL>
 * <DT>Source and Program Elements</DT>
 * <DD>
 * A {@link de.uka.ilkd.key.java.ast.SourceElement} is a syntactical entity and not
 * necessary a {@link de.uka.ilkd.key.java.ast.ModelElement}, such as a {@link de.uka.ilkd.key.java.ast.Comment}.
 * <p>
 * A {@link de.uka.ilkd.key.java.ast.ProgramElement} is a {@link de.uka.ilkd.key.java.ast.SourceElement}
 * and a {@link de.uka.ilkd.key.java.ast.ModelElement}. It is aware of its parent in the syntax
 * tree, while a pure {@link de.uka.ilkd.key.java.ast.SourceElement} is not considered as a
 * member of the AST even though it is represented in the sources.
 * <p>
 * {@link de.uka.ilkd.key.java.ast.ProgramElement}s are further
 * classified into {@link de.uka.ilkd.key.java.ast.TerminalProgramElement}s and
 * {@link de.uka.ilkd.key.java.ast.NonTerminalProgramElement}s. While {@link
 * de.uka.ilkd.key.java.ast.TerminalProgramElement}
 * is just a tag class, {@link de.uka.ilkd.key.java.ast.NonTerminalProgramElement}s know
 * their AST children (while it is possible that they do not have any).
 * A complete source file occurs as a {@link de.uka.ilkd.key.java.ast.CompilationUnit}.
 * <p>
 * {@link de.uka.ilkd.key.java.ast.JavaSourceElement} and
 * {@link de.uka.ilkd.key.java.ast.JavaProgramElement} are abstract classes defining
 * standard implementations that already know their
 * {@link recoder.java.JavaProgramFactory}.
 * </DD>
 * <p>
 * <DT>Expressions and Statements</DT>
 * <DD>
 * {@link de.uka.ilkd.key.java.ast.Expression} and {@link de.uka.ilkd.key.java.ast.Statement} are
 * self-explanatory. A {@link de.uka.ilkd.key.java.ast.LoopInitializer} is a special
 * {@link de.uka.ilkd.key.java.ast.Statement} valid as initializer of
 * {@link de.uka.ilkd.key.java.ast.statement.For} loops.
 * {@link de.uka.ilkd.key.java.ast.LoopInitializer} is subtyped by
 * {@link de.uka.ilkd.key.java.ast.expression.ExpressionStatement} and
 * {@link de.uka.ilkd.key.java.ast.declaration.LocalVariableDeclaration}).
 * <p>
 * Concrete classes and further abstractions are bundled in the
 * {@link de.uka.ilkd.key.java.ast.expression} and {@link de.uka.ilkd.key.java.ast.statement} packages.
 * </DD>
 * <p>
 * <DT>Syntax Tree Parents</DT>
 * <DD>
 * There are a couple of abstractions dealing with properties of being a
 * parent node.
 * <p>
 * These are {@link de.uka.ilkd.key.java.ast.declaration.TypeDeclarationContainer},
 * {@link de.uka.ilkd.key.java.ast.ExpressionContainer},
 * {@link de.uka.ilkd.key.java.ast.StatementContainer},
 * {@link de.uka.ilkd.key.java.ast.ParameterContainer},
 * {@link de.uka.ilkd.key.java.ast.NamedProgramElement} and
 * {@link de.uka.ilkd.key.java.ast.reference.TypeReferenceContainer}. A
 * An {@link de.uka.ilkd.key.java.ast.ExpressionContainer} contains
 * {@link de.uka.ilkd.key.java.ast.Expression}s, a
 * {@link de.uka.ilkd.key.java.ast.StatementContainer} contains
 * {@link de.uka.ilkd.key.java.ast.Statement}s, a
 * {@link de.uka.ilkd.key.java.ast.ParameterContainer}
 * (either a {@link de.uka.ilkd.key.java.ast.declaration.MethodDeclaration} or a
 * {@link de.uka.ilkd.key.java.ast.statement.Catch} statement) contains
 * {@link de.uka.ilkd.key.java.ast.declaration.ParameterDeclaration}s.
 * A {@link de.uka.ilkd.key.java.ast.NamedProgramElement} is a subtype of
 * {@link de.uka.ilkd.key.java.ast.NamedModelElement}.
 * A {@link de.uka.ilkd.key.java.ast.reference.TypeReferenceContainer} contains one or
 * several names, but these are names of types that are referred to explicitely
 * by a {@link de.uka.ilkd.key.java.ast.reference.TypeReference}.
 * </DD>
 * <p>
 * <DT>References</DT>
 * <DD>
 * A {@link de.uka.ilkd.key.java.ast.Reference} is an explicite use of an entity. Most of
 * these {@link de.uka.ilkd.key.java.ast.Reference}s are
 * {@link de.uka.ilkd.key.java.ast.reference.NameReference}s
 * and as such {@link de.uka.ilkd.key.java.ast.NamedProgramElement}s, e.g. the
 * {@link de.uka.ilkd.key.java.ast.reference.TypeReference}.
 * Subtypes of {@link de.uka.ilkd.key.java.ast.Reference}s are bundled in the
 * {@link de.uka.ilkd.key.java.ast.reference} package.
 * </DD>
 * <p>
 * <DT>Modifiers and Declarations</DT>
 * <DD>
 * {@link de.uka.ilkd.key.java.ast.declaration.Modifier}s are (exclusively) used in the
 * context of {@link de.uka.ilkd.key.java.ast.Declaration}s.
 * {@link de.uka.ilkd.key.java.ast.declaration.Modifier}s occur explicitly, since they occur
 * as syntactical tokens that might be indented and commented.
 * {@link de.uka.ilkd.key.java.ast.Declaration}s are either
 * declarations of types or other entities such as
 * {@link de.uka.ilkd.key.java.ast.declaration.MemberDeclaration} or
 * {@link de.uka.ilkd.key.java.ast.declaration.VariableDeclaration}. Concrete
 * {@link de.uka.ilkd.key.java.ast.declaration.Modifier}s and
 * {@link de.uka.ilkd.key.java.ast.Declaration}s are
 * bundled in the {@link de.uka.ilkd.key.java.ast.declaration.modifier} and
 * {@link de.uka.ilkd.key.java.ast.declaration} packages.
 * </DD>
 * </DL>
 *
 * @author Alexander Weigl
 * @version 1 (11/6/21)
 */
package de.uka.ilkd.key.java;