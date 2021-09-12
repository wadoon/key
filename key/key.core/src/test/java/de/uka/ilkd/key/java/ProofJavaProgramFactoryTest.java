package de.uka.ilkd.key.java;

import de.uka.ilkd.key.util.HelperClassForTests;
import org.junit.Assert;
import org.junit.Assume;
import org.junit.Test;
import org.key_project.util.helper.FindResources;
import org.key_project.util.java.IOUtil;
import recoder.ParserException;
import recoder.abstraction.Method;
import recoder.java.Comment;
import recoder.java.CompilationUnit;
import recoder.java.JavaProgramElement;
import recoder.java.Statement;
import recoder.java.StatementBlock;
import recoder.java.declaration.ClassDeclaration;
import recoder.java.declaration.MethodDeclaration;
import recoder.java.declaration.TypeDeclaration;
import recoder.java.statement.EmptyStatement;
import recoder.list.generic.ASTList;

import java.io.File;
import java.io.IOException;
import java.util.Optional;
import java.util.function.Predicate;

/**
 * @author Alexander Weigl
 * @version 1 (9/12/21)
 */
public class ProofJavaProgramFactoryTest {
    final Services services = HelperClassForTests.createServices();
    final Recoder2KeY r2k = new Recoder2KeY(services, services.getNamespaces());

    @Test
    public void testAttachCommentsCompilationUnit() throws IOException, ParserException {
        File inputFile = new File(FindResources.getTestResourcesDirectory(),
                "de/uka/ilkd/key/java/recoderext/AssertsFalse.java");
        final CompilationUnit cu = getCompilationUnit(inputFile);

        Optional<Method> om = findMethod(cu, "AssertsFalse", "m");
        System.out.println(cu);
        Assert.assertTrue("Could not find method AssertsFalse#m()", om.isPresent());
        MethodDeclaration m = (MethodDeclaration) om.get();
        assertContainsComment(m, it -> it.startsWith("/*@ normal_behavior"));

        Statement last = lastStatement(m);
        Assert.assertTrue(last instanceof EmptyStatement);
        assertContainsComment((JavaProgramElement) last, it -> it.equals("//@ assert false;"));
    }

    private Statement lastStatement(MethodDeclaration m) {
        return lastStatement(m.getBody());
    }

    private Statement lastStatement(StatementBlock body) {
        return body.getStatementAt(body.getStatementCount() - 1);
    }

    private void assertContainsComment(JavaProgramElement m, Predicate<String> needle) {
        ASTList<Comment> haystack = m.getComments();
        Optional<Comment> search = haystack.stream()
                .filter(it -> needle.test(it.getText()))
                .findFirst();
        Assert.assertTrue("Could not find comment satisfying the given predicate.",
                search.isPresent());
    }

    private CompilationUnit getCompilationUnit(File inputFile) throws IOException {
        Assume.assumeTrue("Required input file " + inputFile + " does not exists!", inputFile.exists());
        String content = IOUtil.readFrom(inputFile);
        return r2k.recoderCompilationUnits(new String[]{content}).get(0);
    }

    private Optional<Method> findMethod(CompilationUnit cu, String className, String methodName) {
        for (int i = 0; i < cu.getTypeDeclarationCount(); i++) {
            TypeDeclaration td = cu.getTypeDeclarationAt(i);
            if (td instanceof ClassDeclaration) {
                ClassDeclaration clazz = (ClassDeclaration) td;
                if (clazz.getName().equals(className)) {
                    return clazz.getMethods().stream()
                            .filter(it -> it.getName().equals(methodName))
                            .findFirst();
                }
            }
        }
        return Optional.empty();
    }
}
