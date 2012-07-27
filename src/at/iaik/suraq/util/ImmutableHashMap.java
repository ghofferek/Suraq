package at.iaik.suraq.util;

import java.util.Collection;
import java.util.HashMap;
import java.util.Map;
import java.util.Set;

public class ImmutableHashMap<E, V> implements Map<E, V> {

    protected final HashMap<E,V> internalMap;
    
    public ImmutableHashMap(Map<E,V> map)
    {
        internalMap = new HashMap<E,V>(map);
    }
    
    @Override
    @Deprecated
    public void clear() {
        throw new UnsupportedOperationException("clear on immutable map");
    }

    @Override
    public boolean containsKey(Object key) {
        return internalMap.containsKey(key);
    }

    @Override
    public boolean containsValue(Object value) {
        return internalMap.containsValue(value);
    }

    @Override
    public Set<Entry<E,V>> entrySet() {
        return new ImmutableHashSet<Entry<E,V>>(internalMap.entrySet());
    }

    @Override
    public V get(Object key) {
        return internalMap.get(key);
    }

    @Override
    public boolean isEmpty() {
        return internalMap.isEmpty();
    }

    @Override
    public Set<E> keySet() {
        return new ImmutableHashSet<E>(internalMap.keySet());
    }

    @Override
    @Deprecated
    public V put(Object key, Object value) {
        throw new UnsupportedOperationException("put on immutable map");
    }

    @Override
    @Deprecated
    public void putAll(@SuppressWarnings("rawtypes") Map m) {
        throw new UnsupportedOperationException("putAll on immutable map");
        
    }

    @Override
    @Deprecated
    public V remove(Object key) {
        throw new UnsupportedOperationException("remove on immutable map");
    }

    @Override
    public int size() {
        return internalMap.size();
    }

    @Override
    public Collection<V> values() {
        return new ImmutableArrayList<V>(internalMap.values());
    }
    

}
