package de.uka.ilkd.key.gui.specbrowse;

import de.uka.ilkd.key.proof.mgt.SpecificationRepository;
import org.jspecify.annotations.Nullable;

import javax.swing.*;
import javax.swing.tree.DefaultTreeModel;
import javax.swing.tree.TreeNode;
import java.awt.*;
import java.util.List;
import java.util.*;

/**
 * @author Alexander Weigl
 * @version 1 (26.04.24)
 */
public class SpecificationBrowser extends JPanel {
    private final SpecificationRepository repository;
    private final JTree tree = new JTree();
    private final Box introspection = new Box(BoxLayout.Y_AXIS);

    public SpecificationBrowser(SpecificationRepository repository) {
        this.repository = repository;

        setBorder(BorderFactory.createEmptyBorder(5, 5, 5, 5));
        setLayout(new BorderLayout());

        var splitPane = new JSplitPane(JSplitPane.VERTICAL_SPLIT);
        splitPane.setContinuousLayout(true);
        splitPane.setOneTouchExpandable(true);
        splitPane.setDividerLocation(0.4d);
        splitPane.add(new JScrollPane(tree));
        splitPane.add(new JScrollPane(introspection));
        add(splitPane, BorderLayout.CENTER);
        tree.setModel(new DefaultTreeModel(createRoot()));
    }

    private TreeNode createRoot() {
        var root = new LabelTreeNode(null, "Specifications", null);
        repository.getContracts().forEach((k, v) -> {
                    var l = Arrays.stream(k.split("\\.")).toList();
                    var node = root.get(l);
                    v.forEach(c -> node.children.add(new LabelTreeNode(node, c.getName(), c)));
                }
        );

        repository.getLoopContracts().forEach((k, v) -> {
            var block = k.first;
            var loc = k.second;
            var idx = k.third;
            var l = Arrays.stream(loc.toString().split("\\.")).toList();
            var node = root.get(l);
            v.forEach(c -> node.children.add(new LabelTreeNode(node, c.getName(), c)));
        });

        repository.getBlockContracts().forEach((k, v) -> {
            var block = k.first;
            var loc = k.second;
            var idx = k.third;
            var l = Arrays.stream(loc.toString().split("\\.")).toList();
            var node = root.get(l);
            v.forEach(c -> node.children.add(new LabelTreeNode(node, c.getName(), c)));
        });

        repository.getClassInvariants().forEach((k, v) -> {
            var l = Arrays.stream(k.getFullName().split("\\.")).toList();
            var node = root.get(l);
            v.forEach(c -> node.children.add(new LabelTreeNode(node, c.getName(), c)));
        });

        repository.getLoopSpec().forEach((k, v) -> {
            var l = Arrays.stream(k.getFullName().split("\\.")).toList();
            var node = root.get(l);
            v.forEach(c -> node.children.add(new LabelTreeNode(node, c.getName(), c)));
        });
        return root;
    }

    class LabelTreeNode implements TreeNode, Comparable<LabelTreeNode> {
        private static final Comparator<? super LabelTreeNode> sortByLabel = Comparator.comparing(it -> it.label);
        private final TreeNode parent;
        private final String label;
        private final @Nullable Object userData;
        private final List<LabelTreeNode> children = new ArrayList<>(16);

        public LabelTreeNode(TreeNode parent, String label, Object userData) {
            this.parent = parent;
            this.label = label;
            this.userData = userData;
        }

        LabelTreeNode get(List<String> elements) {
            if (elements.isEmpty()) return this;
            var head = elements.removeFirst();

            var c = children.stream().filter(it -> it.label.equals(head)).findAny();
            if (c.isPresent()) {
                return c.get().get(elements);
            } else {
                LabelTreeNode child = new LabelTreeNode(this, head, c);
                children.add(child);
                children.sort(sortByLabel);
                return child.get(elements);
            }
        }

        @Override
        public TreeNode getChildAt(int childIndex) {
            return children.get(childIndex);
        }

        @Override
        public int getChildCount() {
            return children.size();
        }

        @Override
        public TreeNode getParent() {
            return parent;
        }

        @Override
        public int getIndex(TreeNode node) {
            return children.indexOf(node);
        }

        @Override
        public boolean getAllowsChildren() {
            return true;
        }

        @Override
        public boolean isLeaf() {
            return getChildCount() != 0;
        }

        @Override
        public Enumeration<? extends TreeNode> children() {
            return Collections.enumeration(children);
        }

        @Override
        public int compareTo(LabelTreeNode o) {
            return label.compareTo(o.label);
        }
    }

}
