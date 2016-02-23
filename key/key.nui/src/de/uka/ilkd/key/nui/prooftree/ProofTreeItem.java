package de.uka.ilkd.key.nui.prooftree;

import javafx.collections.ObservableList;
import javafx.collections.transformation.FilteredList;
import javafx.scene.control.TreeItem;
import javafx.beans.binding.Bindings;
import javafx.beans.binding.ObjectBinding;
import javafx.beans.property.ObjectProperty;
import javafx.beans.property.SimpleObjectProperty;
import javafx.collections.FXCollections;
import javafx.collections.ListChangeListener;

import java.lang.reflect.Field;
import java.util.concurrent.Callable;
import java.util.function.Predicate;

public class ProofTreeItem extends TreeItem<NUINode> {
    
    /**
     * The internal list for managing children. This is used
     * e. g. to add children.
     */
    private ObservableList<ProofTreeItem> internalChildren;
    
    /**
     * The list that shows children to display. This is a
     * filtered version of internalChildren.
     */
    private FilteredList<ProofTreeItem> filteredChildren;

    /**
     * The predicate that is used for filtering.
     */
    private Predicate<NUINode> filterPredicate;

    public ProofTreeItem(NUINode value) {
        super(value);
        internalChildren = FXCollections.observableArrayList();
        this.filteredChildren = new FilteredList<ProofTreeItem>(internalChildren);
        
        setChildren(filteredChildren);
    }
    
    public void setFilterPredicate(Predicate<NUINode> predicate) {
        this.filterPredicate = predicate;
        
        // create predicate of ProofTreeItem
        Predicate<ProofTreeItem> pred = new Predicate<ProofTreeItem>() {
            @Override
            public boolean test(ProofTreeItem t) {
                if(predicate == null)
                    return true;
                else {
                    return predicate.test(t.getValue());
                }
            }
        };
        
        filteredChildren.setPredicate(pred);
        
        // set predicate of children
        //
        // set only predicate of children if this node is visible??
        // then in case of changes in the tree the visibility is not
        // refeshed. But this is much more efficient. Maybe.
        //if (predicate.test(this.getValue())) {
            filteredChildren.forEach(i -> {
                if(i instanceof ProofTreeItem) {
                    ProofTreeItem j = (ProofTreeItem) i;
                    j.setFilterPredicate(predicate);
                }
            });
        //}

    }
        

    protected void setChildren(ObservableList<ProofTreeItem> list) {
        try {
            Field childrenField = TreeItem.class.getDeclaredField("children");
            childrenField.setAccessible(true);
            childrenField.set(this, list);

            Field declaredField = TreeItem.class.getDeclaredField("childrenListener");
            declaredField.setAccessible(true);
            list.addListener(
                    (ListChangeListener<? super ProofTreeItem>) declaredField
                            .get(this));
        }
        catch (NoSuchFieldException | SecurityException
                | IllegalArgumentException | IllegalAccessException e) {
            throw new RuntimeException("Could not set TreeItem.children", e);
        }
    }
    
    /**
     * Adds a child to the treeItem.
     * @param child the child to add
     */
    public void addChild(ProofTreeItem child) {
        internalChildren.add(child);
    }
    

    /**
     * @return the filterPredicate
     */
    public Predicate<NUINode> getFilterPredicate() {
        return filterPredicate;
    }
}
