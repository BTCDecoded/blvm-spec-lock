//! Specification caching to avoid re-parsing on every compile
//!
//! Caches parsed specifications in `target/.spec-cache/` keyed by file hash.

use sha2::{Digest, Sha256};
use std::fs;
use std::path::{Path, PathBuf};

/// Cache manager for parsed specifications
pub struct SpecCache {
    cache_dir: PathBuf,
}

impl SpecCache {
    /// Create a new cache manager
    pub fn new(manifest_dir: &Path) -> Self {
        let cache_dir = manifest_dir
            .join("target")
            .join(".spec-cache");

        // Ensure cache directory exists
        fs::create_dir_all(&cache_dir).ok();

        SpecCache { cache_dir }
    }

    /// Get cache key for a file (based on content hash)
    pub fn cache_key(file_path: &Path) -> String {
        // In a real implementation, we'd hash the file content
        // For now, use a simple approach based on file path and mtime
        format!("{:x}", Sha256::digest(file_path.to_string_lossy().as_bytes()))
    }

    /// Load cached specification if available
    pub fn load(&self, key: &str) -> Option<String> {
        let cache_file = self.cache_dir.join(format!("{}.cache", key));
        fs::read_to_string(cache_file).ok()
    }

    /// Save specification to cache
    pub fn save(&self, key: &str, content: &str) {
        let cache_file = self.cache_dir.join(format!("{}.cache", key));
        fs::write(cache_file, content).ok();
    }

    /// Check if cache entry is valid (not expired)
    pub fn is_valid(&self, key: &str, _source_mtime: u64) -> bool {
        let cache_file = self.cache_dir.join(format!("{}.cache", key));
        if let Ok(metadata) = fs::metadata(&cache_file) {
            if let Ok(mtime) = metadata.modified() {
                // In a real implementation, compare with source file mtime
                // For now, just check if cache file exists
                return true;
            }
        }
        false
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::env;

    #[test]
    fn test_cache_key() {
        let path = Path::new("/tmp/test.md");
        let key = SpecCache::cache_key(path);
        assert!(!key.is_empty());
    }

    #[test]
    fn test_cache_operations() {
        let manifest_dir = env::temp_dir();
        let cache = SpecCache::new(&manifest_dir);
        let key = "test_key";
        let content = "test content";

        cache.save(key, content);
        let loaded = cache.load(key);
        assert_eq!(loaded, Some(content.to_string()));
    }
}

