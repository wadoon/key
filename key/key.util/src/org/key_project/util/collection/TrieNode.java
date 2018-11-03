package org.key_project.util.collection;

import java.util.Iterator;

interface TrieNode<S, T>{
    Entry<S, T> find(S key, int level);
    TrieNode<S, T> add(Entry<S, T> entry, int level);
    TrieNode<S, T> remove(S key, int level);
    int size();

    static final TrieNode EMPTY = new ListNode(ImmutableSLList.nil());


    static class Entry<S,T> implements ImmutableMapEntry<S,T> {
        private final S key;
        private final T value;

        /** creates a new map entry that contains key and value */
        Entry(S key, T value) {
            this.key   = key;
            this.value = value;
        }

        public S key() {
            return key;
        }

        public T value() {
            return value;
        }

        public int hashCode() {
            return key.hashCode() * 7 + value.hashCode();
        }

        public String toString() {
            return key+"->"+value;
        }
    }

    static class ListNode<S, T> implements TrieNode<S,T> {

        private static final int MAX_SIZE = 10;

        private final ImmutableList<Entry<S, T>> entries;

        private ListNode(ImmutableList<Entry<S, T>> entries) {
            this.entries = entries;
        }

        @Override
        public Entry<S, T> find(S key, int level) {
            for (Entry<S, T> entry : entries) {
                if(entry.key.equals(key)) {
                    return entry;
                }
            }
            return null;
        }

        @Override
        public TrieNode<S, T> add(Entry<S,T> entry, int level) {

            // remove previous entry
            ImmutableList<Entry<S,T>> localEntries = removeFromList(entry.key);

            ImmutableList<Entry<S, T>> prepend = localEntries.prepend(entry);

            if(level < 6 && entries.size() >= MAX_SIZE) {
                return new BroadNode<>(prepend, level);
            } else {
                return new ListNode<>(prepend);
            }
        }

        @Override
        public TrieNode<S, T> remove(S key, int level) {
            ImmutableList<Entry<S, T>> result = removeFromList(key);
            if(result == entries) {
                return this;
            }
            return new ListNode<>(result);
        }

        private ImmutableList<Entry<S, T>> removeFromList(S key) {
            ImmutableList<Entry<S,T>> stack = ImmutableSLList.nil();
            ImmutableList<Entry<S,T>> result = entries;

            while(!result.isEmpty()) {

                Entry<S, T> head = result.head();

                if(head.key.equals(key)) {
                    break;
                }

                result = result.tail();
                stack = stack.prepend(head);
            }

            if(result.isEmpty()) {
                // not found
                return entries;
            }

            result = result.tail();
            while(!stack.isEmpty()) {
                result = result.prepend(stack.head());
                stack = stack.tail();
            }

            return result;
        }

        @Override
        public int size() {
            return entries.size();
        }

    }

    static class BroadNode<S, T> implements TrieNode<S,T> {

        private final TrieNode<S,T>[] table;
        private final int size;

        @SuppressWarnings("unchecked")
        BroadNode(ImmutableList<Entry<S, T>> list, int level) {
            this.size = list.size();
            this.table = new TrieNode[32];
            for(Entry<S,T> en : list) {
                int index = (en.key.hashCode() >> 5*level) & 0x1f;
                if(table[index] == null) {
                    table[index] = new ListNode<S,T>(ImmutableSLList.<Entry<S,T>>nil().prepend(en));
                } else {
                    table[index] = table[index].add(en, level + 1);
                }
            }

        }

        BroadNode(BroadNode<S, T> parent, int index, TrieNode<S, T> update) {
            this.table = parent.table.clone();
            this.table[index] = update;
            TrieNode<S, T> oldnode = parent.table[index];
            int oldsize = oldnode == null ? 0 : oldnode.size();
            this.size = parent.size() - oldsize + update.size();
        }

        @Override
        public Entry<S, T> find(S key, int level) {
            int index = (key.hashCode() >> 5*level) & 0x1f;
            if(table[index] == null) {
                return null;
            }
            return table[index].find(key, level+1);
        }

        @Override
        public TrieNode<S, T> add(Entry<S, T> entry, int level) {
            int index = (entry.key.hashCode() >> 5*level) & 0x1f;
            TrieNode<S, T> changed;

            if(table[index] == null) {
                changed = new ListNode<S,T>(ImmutableSLList.<Entry<S,T>>nil().prepend(entry));
            } else {
                changed = table[index].add(entry, level + 1);
            }

            if(changed == table[index]) {
                return this;
            } else {
                return new BroadNode<S,T>(this, index, changed);
            }
        }

        @Override
        public BroadNode<S, T> remove(S key, int level) {
            int index = (key.hashCode() >> 5*level) & 0x1f;
            if(table[index] == null) {
                return this;
            }

            TrieNode<S, T> changed = table[index].remove(key, level + 1);

            if(changed == table[index]) {
                return this;
            } else {
                return new BroadNode<S,T>(this, index, changed);
            }
        }

        @Override
        public int size() {
            return size;
        }

    }

//    static class Iter<S,T> implements Iterator<ImmutableMapEntry<S, T>> {
//        private final Node<S,T>[] table;
//        private int pos = 0;
//        private Iterator<ImmutableMapEntry<S, T>> innerIt;
//
//        private Iter(Node<S, T>[] table) {
//            this.table = table;
//        }
//
//        @Override
//        public boolean hasNext() {
//
//            do {
//                if(innerIt == null) {
//                    while(pos < table.length &&  table[pos] == null) {
//                        pos ++;
//                    }
//                    if(pos == table.length) {
//                        return false;
//                    }
//                    innerIt = table[pos].iterator();
//                }
//
//                boolean result = innerIt.hasNext();
//                if(result) {
//                    return true;
//                }
//
//                innerIt = null;
//            } while(true);
//        }
//
//        @Override
//        public ImmutableMapEntry<S, T> next() {
//            return innerIt.next();
//        }
//
//        @Override
//        public void remove() {
//            innerIt.remove();
//        }
//    }


}
