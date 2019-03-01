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


import edu.kit.iti.formal.psdbg.parser.ScriptLanguageParser;
import edu.kit.iti.formal.psdbg.parser.Visitable;
import edu.kit.iti.formal.psdbg.parser.Visitor;
import lombok.NoArgsConstructor;
import lombok.ToString;

import java.util.*;
import java.util.function.Consumer;
import java.util.function.Predicate;
import java.util.function.UnaryOperator;
import java.util.stream.Stream;

/**
 * @author Alexander Weigl
 * @version 1 (27.04.17)
 */
@ToString
@NoArgsConstructor
public class Statements extends ASTNode<ScriptLanguageParser.StmtListContext>
        implements Visitable, Iterable<Statement> {
    private final List<Statement> statements = new ArrayList<>();

    @Override
    public ASTNode[] getChildren() {
        return (ASTNode[]) toArray();
    }

    public Statements(Statements body) {
        statements.addAll(body.statements);
    }

    public Iterator<Statement> iterator() {
        return statements.iterator();
    }

    public int size() {
        return statements.size();
    }

    public boolean isEmpty() {
        return statements.isEmpty();
    }

    public boolean contains(Object o) {
        return statements.contains(o);
    }

    public Object[] toArray() {
        return statements.toArray();
    }

    public <T> T[] toArray(T[] a) {
        return statements.toArray(a);
    }

    public boolean add(Statement statement) {
        if (statement == null)
            throw new NullPointerException();
        statement.setParent(this);
        return statements.add(statement);
    }

    public boolean remove(Object o) {
        return statements.remove(o);
    }

    public boolean containsAll(Collection<?> c) {
        return statements.containsAll(c);
    }

    public boolean addAll(Collection<? extends Statement> c) {
        return statements.addAll(c);
    }

    public boolean addAll(int index, Collection<? extends Statement> c) {
        return statements.addAll(index, c);
    }

    public boolean removeAll(Collection<?> c) {
        return statements.removeAll(c);
    }

    public boolean retainAll(Collection<?> c) {
        return statements.retainAll(c);
    }

    public void replaceAll(UnaryOperator<Statement> operator) {
        statements.replaceAll(operator);
    }

    public void sort(Comparator<? super Statement> c) {
        statements.sort(c);
    }

    public void clear() {
        statements.clear();
    }

    public Statement get(int index) {
        return statements.get(index);
    }

    public Statement set(int index, Statement element) {
        return statements.set(index, element);
    }

    public void add(int index, Statement element) {
        statements.add(index, element);
    }

    public Statement remove(int index) {
        return statements.remove(index);
    }

    public int indexOf(Object o) {
        return statements.indexOf(o);
    }

    public int lastIndexOf(Object o) {
        return statements.lastIndexOf(o);
    }

    public ListIterator<Statement> listIterator() {
        return statements.listIterator();
    }

    public ListIterator<Statement> listIterator(int index) {
        return statements.listIterator(index);
    }

    public List<Statement> subList(int fromIndex, int toIndex) {
        return statements.subList(fromIndex, toIndex);
    }

    public boolean removeIf(Predicate<? super Statement> filter) {
        return statements.removeIf(filter);
    }

    public Stream<Statement> stream() {
        return statements.stream();
    }

    public Stream<Statement> parallelStream() {
        return statements.parallelStream();
    }

    public void forEach(Consumer<? super Statement> action) {
        statements.forEach(action);
    }

    @Override
    public String toString() {
        return "Statements{" + "statements=" + statements + '}';
    }

    @Override
    public <T> T accept(Visitor<T> visitor) {
        return visitor.visit(this);
    }

    @Override
    public Statements copy() {
        Statements s = new Statements();
        forEach(e -> {
            Statement ecopy = e.copy();
            ecopy.setRuleContext(e.getRuleContext());
            s.add(ecopy);
        });
        s.setRuleContext(this.getRuleContext());
        return s;
    }

    @Override
    public boolean eq(ASTNode o) {
        if (this == o) return true;
        if (!(o instanceof Statements)) return false;
        if (!super.equals(o)) return false;
        Statements that = (Statements) o;
        for (int i = 0; i < statements.size(); i++) {
            if (!statements.get(i).eq(that.statements.get(i))) {
                return false;
            }
        }
        return true;
    }
}
