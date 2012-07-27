package at.iaik.suraq.util;

import java.lang.ref.WeakReference;
import java.util.ArrayList;
import java.util.TreeMap;

import at.iaik.suraq.sexp.Token;
import at.iaik.suraq.smtlib.formula.*;

public class FormulaCache<T> {
	// This static List MUST be on first position in this file!
	// Else it would not be initialized before the other static variables
	private static ArrayList<FormulaCache<?>> instances = new ArrayList<FormulaCache<?>>();

	public static FormulaCache<Token> token = new FormulaCache<Token>("Token", true);
	public static FormulaCache<NotFormula> notFormula = new FormulaCache<NotFormula>("NOT", true);
	public static FormulaCache<AndFormula> andFormula = new FormulaCache<AndFormula>("AND", true);
	public static FormulaCache<OrFormula> orFormula = new FormulaCache<OrFormula>("OR", true);
	public static FormulaCache<PropositionalVariable> propVar = new FormulaCache<PropositionalVariable>("PropVar", true);
	public static FormulaCache<ImpliesFormula> impliesFormula = new FormulaCache<ImpliesFormula>("implies", true);
	
	public static boolean _isActive = false;
	public boolean _isActive2 = true;
	
	// For statistics
	private int cachedReads = 0;
	
	
	// Sets are not possible, because they don't provide the get() method
	
	// WeakHashMap is not possible, because it does not use Hashes
	// TODO: WeakHashMap compares keys with equals(==) instead of .hashCode!!!!
	// http://docs.oracle.com/javase/6/docs/api/java/util/WeakHashMap.html
	
	// Use a TreeMap, where the Key is the HashCode of the Objects
	private TreeMap<Integer, WeakReference<T>> cache = new TreeMap<Integer, WeakReference<T>>();
	private String name; 
	
	private FormulaCache(String name, boolean isActive2)
	{
		this._isActive2 = isActive2;
		try{
			this.name = name;
			FormulaCache.instances.add(this);
		}
		catch(Exception ex)
		{
			ex.printStackTrace();
			throw new RuntimeException("blubb");
		}
	}
	
	/**
	 * Clears all caches.
	 */
	public static void clearAll()
	{
		for(FormulaCache<?> instance : instances)
		{
			instance.clear();
		}
	}
	
	/**
	 * Clears the cache and resets the statistic.
	 */
	public void clear()
	{
		cache.clear();
		cachedReads = 0;
	}
	
	/**
	 * This may override an existing object with the same hashCode.
	 * @param object
	 * @throws ClassCastException
	 */
	public void post(T object) throws ClassCastException
	{
		if(!_isActive || ! _isActive2) return;
		cache.put(object.hashCode(), new WeakReference<T>(object));
	}
	
	/**
	 * This method returns an Object with the same hashCode if it already exists.
	 * If not, the given Object is stored in the Map.
	 * If you modify the given Object later, it will be changed everywhere!!!
	 * @param object
	 * @return
	 * @throws ClassCastException
	 */
	public T put(T object) throws ClassCastException
	{
		if(!_isActive || ! _isActive2) return object;
		int hash = object.hashCode();
		//type.cast(reference);
		if(cache.containsKey(hash))
		{
			T result = cache.get(hash).get();
			if(result != null)
			{
				if(result != object)
					cachedReads++;
				return result;
			}
		}
		cache.put(hash, new WeakReference<T>(object));
		return object;
	}
	
	/**
	 * Gets an already existing instance of the given reference object.
	 * If the Object does not exist, this method returns null
	 * @param reference
	 * @return
	 * @throws ClassCastException
	 */
	public T get(T reference) throws ClassCastException
	{
		if(!_isActive || ! _isActive2) return reference;
		int hash = reference.hashCode();
		if(cache.containsKey(hash))
		{
			T result = cache.get(hash).get();
			if(result != reference && result != null)
				cachedReads++;
			return result;
		}
		return null;
	}
	
	public int getCachedReads()
	{
		return cachedReads;
	}
	public int getCachedElements()
	{
		return cache.size();
	}
	public String getName()
	{
		return name;
	}
	
	public static void printStatistic()
	{
		System.out.println("************************************************");
		for(FormulaCache<?> instance : instances)
		{
			int reads = instance.getCachedReads();
			int elems = instance.getCachedElements();
			String className = instance.getName();
			System.out.println("* saved "+ reads + " reads on " + elems + " elements:" + className);
		}
		System.out.println("************************************************");
	}
	
}
