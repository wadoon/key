package de.uka.ilkd.key.strategy;

import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.concurrent.locks.ReentrantReadWriteLock;
import java.util.concurrent.locks.ReentrantReadWriteLock.ReadLock;
import java.util.concurrent.locks.ReentrantReadWriteLock.WriteLock;

import org.key_project.util.LRUCache;
import org.key_project.util.collection.ImmutableArray;

import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.rule.IfFormulaInstantiation;

/**
 * Direct-mapped cache of lists of formulas (potential instantiations of
 * if-formulas of taclets) that were modified after a certain point of time
 * 
 * Hashmaps of the particular lists of formulas; the keys of the maps is the
 * point of time that separates old from new (modified) formulas
 *
 * Keys: Long Values: IList<IfFormulaInstantiation>
 */
public class IfInstantiationCachePool {

    public final LRUCache<Node, IfInstantiationCache> cacheMgr = new LRUCache<>(10);
    /**
     * 
     * read/write lock for cache access to avoid unnecessary locking
     */
    private final ReentrantReadWriteLock rw_lock = new ReentrantReadWriteLock();
    private final ReadLock read_lock = rw_lock.readLock();
    private final WriteLock write_lock = rw_lock.writeLock();

    public IfInstantiationCache getCache(Node n) {
        IfInstantiationCache cache;
        try {
            read_lock.lock();
            cache = cacheMgr.get(n);
        } finally {
            read_lock.unlock();
        }

        if (cache != null) {
            return cache;
        }

        cache = new IfInstantiationCache();

        IfInstantiationCache cache2;
        try {
            write_lock.lock();
            cache2 = cacheMgr.putIfAbsent(n, cache);
        } finally {
            write_lock.unlock();
        }

        if (cache2 != null) {
            cache = cache2;
        }

        return cache;
    }

    public void releaseAll() {
        synchronized(cacheMgr) {
            cacheMgr.clear();
        }
    }  

    public void release(Node n) {
        IfInstantiationCache cache = null;
        synchronized(cacheMgr) {
            cache = cacheMgr.remove(n);           
        }
        if (cache != null) {
            cache.reset();
        }
    }

    public static class IfInstantiationCache {

        private final HashMap<Long, ImmutableArray<IfFormulaInstantiation>> antecCache = new LinkedHashMap<>();
        private final HashMap<Long, ImmutableArray<IfFormulaInstantiation>> succCache = new LinkedHashMap<>();

        private final ReentrantReadWriteLock lock = new ReentrantReadWriteLock();
        private final ReadLock readLock = lock.readLock();
        private final WriteLock writeLock = lock.writeLock();

        public ImmutableArray<IfFormulaInstantiation> get(boolean antec, Long key) {
            try {
                readLock.lock();
                final HashMap<Long, ImmutableArray<IfFormulaInstantiation>> cache = antec
                        ? antecCache
                                : succCache;
                return cache.get(key);
            } finally {
                readLock.unlock();
            }
        }

        public void put(boolean antec, Long key, ImmutableArray<IfFormulaInstantiation> value) {
            final HashMap<Long, ImmutableArray<IfFormulaInstantiation>> cache = antec
                    ? antecCache
                            : succCache;
            try {
                writeLock.lock();
                cache.put(key, value);
            } finally {
                writeLock.unlock();
            }
        }

        private void reset() {
            try {
                writeLock.lock();
                antecCache.clear();
                succCache.clear();
            } finally {
                writeLock.unlock();
            }
        }
    }
}