package de.uka.ilkd.key.strategy;

import java.util.HashMap;
import java.util.concurrent.locks.ReentrantReadWriteLock;
import java.util.concurrent.locks.ReentrantReadWriteLock.ReadLock;
import java.util.concurrent.locks.ReentrantReadWriteLock.WriteLock;

import org.key_project.util.LRUCache;
import org.key_project.util.collection.ImmutableList;

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
public final class IfInstantiationCachePool {

    private final LRUCache<Node, IfInstantiationCache> cacheMgr = new LRUCache<>(20);
    
    private final ReentrantReadWriteLock cacheMgrlock = new ReentrantReadWriteLock();
    private final ReadLock readMgrLock = cacheMgrlock.readLock();
    private final WriteLock writeMgrLock = cacheMgrlock.writeLock();

    public final IfInstantiationCache getCache(Node n) {
        IfInstantiationCache cache;
        
        try {
            readMgrLock.lock();
            cache = cacheMgr.get(n);
        } finally {
            readMgrLock.unlock();
        }
        
        if (cache != null) {
            return cache;
        }
        
        cache = new IfInstantiationCache();
        
        IfInstantiationCache cache2;

        try {
            writeMgrLock.lock();
            cache2 = cacheMgr.putIfAbsent(n, cache);
        } finally {
            writeMgrLock.unlock();
        }
        
        if (cache2 != null) {
            cache = cache2;
        }
        
        return cache;
    }
    
    public final void releaseAll() {
        try {
            writeMgrLock.lock();
            cacheMgr.clear();
        } finally {
            writeMgrLock.unlock();
        }
    }  
    
    public final void release(Node n) {
        try {
            writeMgrLock.lock();
            cacheMgr.remove(n);           
        } finally {
            writeMgrLock.unlock();
        }
    }
    
    public final static class IfInstantiationCache {

        private final HashMap<Long, ImmutableList<IfFormulaInstantiation>> antecCache = new HashMap<>();
        private final HashMap<Long, ImmutableList<IfFormulaInstantiation>> succCache  = new HashMap<>();

        private final ReentrantReadWriteLock lock = new ReentrantReadWriteLock();
        private final ReadLock readLock = lock.readLock();
        private final WriteLock writeLock = lock.writeLock();

        public final ImmutableList<IfFormulaInstantiation> get(boolean antec, Long key) {
            try {
                readLock.lock();
                final HashMap<Long, ImmutableList<IfFormulaInstantiation>> cache = antec
                        ? antecCache
                        : succCache;
                return cache.get(key);
            } finally {
                readLock.unlock();
            }
        }

        public final void put(boolean antec, Long key, ImmutableList<IfFormulaInstantiation> value) {
            final HashMap<Long, ImmutableList<IfFormulaInstantiation>> cache = antec 
                    ? antecCache : succCache;
            try {
                writeLock.lock();
                
                cache.put(key, value);
            } finally {
                writeLock.unlock();
            }
        }

        public final void reset() {
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