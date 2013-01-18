/*
 * Copyright (C) 2009-2012 University of Freiburg
 *
 * This file is part of SMTInterpol.
 *
 * SMTInterpol is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * SMTInterpol is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with SMTInterpol.  If not, see <http://www.gnu.org/licenses/>.
 */
package de.uni_freiburg.informatik.ultimate.smtinterpol.util;

import java.util.AbstractMap;
import java.util.AbstractSet;
import java.util.IdentityHashMap;
import java.util.Iterator;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.util.ScopeUtils;

/**
 * A scoped map implementation based on identity maps.  This map violates the
 * map contract in the same way as IdentityHashMap does.
 * 
 * Null values are not permitted.
 * @author Juergen Christ
 */
public class ScopedIdentityHashMap<K, V> extends AbstractMap<K, V> {

	IdentityHashMap<K, V> m_map;
	IdentityHashMap<K, V>[] m_history;
	int m_curScope = -1;

	@SuppressWarnings("unchecked")
	public ScopedIdentityHashMap() {
		m_map = new IdentityHashMap<K, V>();
		m_history = new IdentityHashMap[ScopeUtils.NUM_INITIAL_SCOPES];
	}

	private IdentityHashMap<K, V> undoMap() {
		return m_history[m_curScope];
	}

	private void recordUndo(K key, V value) {
		if (m_curScope != -1) {
			Map<K, V> old = undoMap();
			if (!old.containsKey(key))
				old.put(key, value);
		}
	}

	private void undoEntry(Entry<K,V> old) {
		if (old.getValue() != null) {
			m_map.put(old.getKey(), old.getValue());
		} else {
			m_map.remove(old.getKey());
		}
	}

	public void beginScope() {
		if (m_curScope == m_history.length - 1)
			m_history = ScopeUtils.grow(m_history);
		m_history[++m_curScope] = new IdentityHashMap<K, V>();
	}

	public void endScope() {
		for (Entry<K, V> old : undoMap().entrySet()) {
			undoEntry(old);
		}
		m_history[m_curScope--] = null;
		if (ScopeUtils.shouldShrink(m_history))
			m_history = ScopeUtils.shrink(m_history);
	}

	public Iterable<Map.Entry<K, V>> currentScopeEntries() {
		if (m_curScope == -1)
			return entrySet();
		return new AbstractSet<Map.Entry<K, V>>() {
			@Override
			public Iterator<Map.Entry<K, V>> iterator() {
				return new Iterator<Map.Entry<K, V>>() {
					Iterator<Entry<K, V>> m_backing = undoMap().entrySet().iterator();
					Entry<K, V> m_last;

					@Override
					public boolean hasNext() {
						return m_backing.hasNext();
					}

					@Override
					public Map.Entry<K, V> next() {
						final K key = (m_last = m_backing.next()).getKey();
						return new Entry<K, V>() {
							@Override
							public K getKey() {
								return key;
							}

							@Override
							public V getValue() {
								return m_map.get(key);
							}

							@Override
							public V setValue(V value) {
								return m_map.put(key, value);
							}
						};
					}

					@Override
					public void remove() {
						m_backing.remove();
						undoEntry(m_last);
					}
				};
			}

			@Override
			public int size() {
				return undoMap().size();
			}
		};
	}

	public Iterable<K> currentScopeKeys() {
		if (m_curScope == -1)
			return keySet();
		return new AbstractSet<K>() {
			@Override
			public Iterator<K> iterator() {
				return new Iterator<K>() {

					Iterator<Entry<K, V>> m_backing = undoMap().entrySet().iterator();
					Entry<K, V> m_last;

					@Override
					public boolean hasNext() {
						return m_backing.hasNext();
					}

					@Override
					public K next() {
						return (m_last = m_backing.next()).getKey();
					}

					@Override
					public void remove() {
						m_backing.remove();
						undoEntry(m_last);
					}
				};
			}

			@Override
			public int size() {
				return undoMap().size();
			}
		};
	}

	public Iterable<V> currentScopeValues() {
		if (m_curScope == -1)
			return values();
		return new AbstractSet<V>() {
			@Override
			public Iterator<V> iterator() {
				return new Iterator<V>() {

					Iterator<Entry<K, V>> m_backing = undoMap().entrySet().iterator();
					Entry<K, V> m_last;

					@Override
					public boolean hasNext() {
						return m_backing.hasNext();
					}

					@Override
					public V next() {
						return m_map.get((m_last = m_backing.next()).getKey());
					}

					@Override
					public void remove() {
						m_backing.remove();
						undoEntry(m_last);
					}
				};
			}

			@Override
			public int size() {
				return undoMap().size();
			}
		};
	}

	@SuppressWarnings("unchecked")
	@Override
	public void clear() {
		m_map.clear();
		m_history = new IdentityHashMap[ScopeUtils.NUM_INITIAL_SCOPES];
	}

	@Override
	public boolean containsKey(Object key) {
		return m_map.containsKey(key);
	}

	@Override
	public boolean containsValue(Object value) {
		return m_map.containsValue(value);
	}

	@Override
	public V get(Object key) {
		return m_map.get(key);
	}

	@Override
	public boolean isEmpty() {
		return m_map.isEmpty();
	}

	public boolean isEmptyScope() {
		return m_curScope == -1;
	}

	@Override
	public Set<Entry<K,V>> entrySet() {
		return new AbstractSet<Entry<K,V>>() {

			@Override
			public Iterator<Entry<K,V>> iterator() {
				return new Iterator<Entry<K,V>>() {

					Iterator<Entry<K,V>> m_backing = m_map.entrySet().iterator();
					Entry<K,V> m_last;

					@Override
					public boolean hasNext() {
						return m_backing.hasNext();
					}

					@Override
					public Entry<K,V> next() {
						return m_last = m_backing.next();
					}

					@Override
					public void remove() {
						m_backing.remove();
						recordUndo(m_last.getKey(), m_last.getValue());
					}
				};
			}

			@Override
			public int size() {
				return m_map.size();
			}
		};
	}

	@Override
	public V put(K key, V value) {
		if (value == null)
			throw new NullPointerException();
		V oldval = m_map.put(key, value);
		recordUndo(key, oldval);
		return oldval;
	}

	@SuppressWarnings("unchecked")
	@Override
	public V remove(Object key) {
		V oldval = m_map.remove(key);
		recordUndo((K) key, oldval);
		return oldval;
	}

	@Override
	public int size() {
		return m_map.size();
	}

	public int currentScopeSize() {
		return undoMap().size();
	}

	public int getActiveScopeNum() {
		return m_curScope + 1;
	}
}
