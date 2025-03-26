#![deny(missing_docs)]
//! This crate is for setting environment variables temporarily.
//!
//! It is useful for testing with different environment variables that should not interfere.
//!
//! # Examples
//!
//! ```rust
//! temp_env::with_var("MY_ENV_VAR", Some("production"), || {
//!     // Run some code where `MY_ENV_VAR` set to `"production"`.
//! });
//!
//! temp_env::with_vars(
//!     [
//!         ("FIRST_VAR", Some("Hello")),
//!         ("SECOND_VAR", Some("World!")),
//!     ],
//!     || {
//!         // Run some code where `FIRST_VAR` is set to `"Hello"` and `SECOND_VAR` is set to
//!         // `"World!"`.
//!     }
//! );
//!
//! temp_env::with_vars(
//!     [
//!         ("FIRST_VAR", Some("Hello")),
//!         ("SECOND_VAR", None),
//!     ],
//!     || {
//!         // Run some code where `FIRST_VAR` is set to `"Hello"` and `SECOND_VAR` is unset (even if
//!         // it was set before)
//!     }
//! );
//! ```
//!
//! It's possible the closure returns a value:
//!
//! ```rust
//! let s = temp_env::with_var("INNER_ENV_VAR", Some("inner value"), || {
//!      std::env::var("INNER_ENV_VAR").unwrap()
//! });
//! println!("{}", s);
//! ```
//!

use std::collections::HashMap;
use std::env;
use std::ffi::{OsStr, OsString};
use std::hash::Hash;

use parking_lot::{ReentrantMutex, ReentrantMutexGuard};

/// Make sure that the environment isn't modified concurrently.
static SERIAL_TEST: ReentrantMutex<()> = ReentrantMutex::new(());

/// Sets a single environment variable for the duration of the closure.
///
/// The previous value is restored when the closure completes or panics, before unwinding the
/// panic.
///
/// If `value` is set to `None`, then the environment variable is unset.
pub fn with_var<K, V, F, R>(key: K, value: Option<V>, closure: F) -> R
where
    K: AsRef<OsStr> + Clone + Eq + Hash,
    V: AsRef<OsStr> + Clone,
    F: FnOnce() -> R,
{
    with_vars([(key, value)], closure)
}

/// Unsets a single environment variable for the duration of the closure.
///
/// The previous value is restored when the closure completes or panics, before unwinding the
/// panic.
///
/// This is a shorthand and identical to the following:
/// ```rust
/// temp_env::with_var("MY_ENV_VAR", None::<&str>, || {
///     // Run some code where `MY_ENV_VAR` is unset.
/// });
/// ```
pub fn with_var_unset<K, F, R>(key: K, closure: F) -> R
where
    K: AsRef<OsStr> + Clone + Eq + Hash,
    F: FnOnce() -> R,
{
    with_var(key, None::<&str>, closure)
}

struct RestoreEnv<'a> {
    env: HashMap<&'a OsStr, Option<OsString>>,
    _guard: ReentrantMutexGuard<'a, ()>,
}

impl<'a> RestoreEnv<'a> {
    /// Capture the given variables from the environment.
    ///
    /// `guard` holds a lock on the shared mutex for exclusive access to the environment, to make
    /// sure that the environment gets restored while the lock is still held, i.e the current
    /// thread still has exclusive access to the environment.
    fn capture<I>(guard: ReentrantMutexGuard<'a, ()>, vars: I) -> Self
    where
        I: Iterator<Item = &'a OsStr> + 'a,
    {
        let env = vars.map(|v| (v, env::var_os(v))).collect();
        Self { env, _guard: guard }
    }
}

impl Drop for RestoreEnv<'_> {
    fn drop(&mut self) {
        for (var, value) in self.env.iter() {
            update_env(var, value.as_ref().map(|v| v.as_os_str()));
        }
    }
}

/// Sets environment variables for the duration of the closure.
///
/// The previous values are restored when the closure completes or panics, before unwinding the
/// panic.
///
/// If a `value` is set to `None`, then the environment variable is unset.
///
/// If the variable with the same name is set multiple times, the last one wins.
pub fn with_vars<K, V, F, R>(kvs: impl AsRef<[(K, Option<V>)]>, closure: F) -> R
where
    K: AsRef<OsStr> + Clone + Eq + Hash,
    V: AsRef<OsStr> + Clone,
    F: FnOnce() -> R,
{
    let old_env = RestoreEnv::capture(
        SERIAL_TEST.lock(),
        kvs.as_ref().iter().map(|(k, _)| k.as_ref()),
    );
    for (key, value) in kvs.as_ref() {
        update_env(key, value.as_ref());
    }
    let retval = closure();
    drop(old_env);
    retval
}

/// Unsets environment variables for the duration of the closure.
///
/// The previous values are restored when the closure completes or panics, before unwinding the
/// panic.
///
/// This is a shorthand and identical to the following:
/// ```rust
/// temp_env::with_vars(
///     [
///         ("FIRST_VAR", None::<&str>),
///         ("SECOND_VAR", None::<&str>),
///     ],
///     || {
///         // Run some code where `FIRST_VAR` and `SECOND_VAR` are unset (even if
///         // they were set before)
///     }
/// );
/// ```
pub fn with_vars_unset<K, F, R>(keys: impl AsRef<[K]>, closure: F) -> R
where
    K: AsRef<OsStr> + Clone + Eq + Hash,
    F: FnOnce() -> R,
{
    let kvs = keys
        .as_ref()
        .iter()
        .map(|key| (key, None::<&str>))
        .collect::<Vec<_>>();
    with_vars(kvs, closure)
}

fn update_env<K, V>(key: K, value: Option<V>)
where
    K: AsRef<OsStr>,
    V: AsRef<OsStr>,
{
    match value {
        Some(v) => unsafe { env::set_var(key, v) },
        None => unsafe { env::remove_var(key) },
    }
}

#[cfg(feature = "async_closure")]
/// Does the same as [`with_vars`] but it allows to pass an async closures.
///
/// ```rust
/// async fn check_var() {
///     let v = std::env::var("MY_VAR").unwrap();
///     assert_eq!(v, "ok".to_owned());
/// }
///
/// #[cfg(feature = "async_closure")]
/// #[tokio::test]
/// async fn test_async_closure() {
///     crate::async_with_vars([("MY_VAR", Some("ok"))], check_var());
/// }
/// ```
pub async fn async_with_vars<K, V, F, R>(kvs: impl AsRef<[(K, Option<V>)]>, closure: F) -> R
where
    K: AsRef<OsStr> + Clone + Eq + Hash,
    V: AsRef<OsStr> + Clone,
    F: std::future::Future<Output = R> + std::future::IntoFuture<Output = R>,
{
    let old_env = RestoreEnv::capture(
        SERIAL_TEST.lock(),
        kvs.as_ref().iter().map(|(k, _)| k.as_ref()),
    );
    for (key, value) in kvs.as_ref() {
        update_env(key, value.as_ref());
    }
    let retval = closure.await;
    drop(old_env);
    retval
}

#[cfg(test)]
mod tests {
    use std::env::VarError;
    use std::sync::atomic::{AtomicUsize, Ordering};
    use std::{env, panic};

    /// Generates unique String for use in tests below.
    /// (we need to prevent collision of environment variable keys to make the tests non-flaky).
    struct UniqueEnvKeyValGen {
        counter: AtomicUsize,
    }

    impl UniqueEnvKeyValGen {
        fn next(&self) -> String {
            let id = self.counter.fetch_add(1, Ordering::SeqCst);
            let key = format!("TEMP_ENV_KEY_{}", id);
            let actual_val = env::var(key.clone());
            assert_eq!(
                Err(VarError::NotPresent),
                actual_val,
                "Test setup broken. {} environment variable is already set to {:?}",
                key,
                actual_val
            );
            key.to_string()
        }
    }

    static GENERATOR: UniqueEnvKeyValGen = UniqueEnvKeyValGen {
        counter: AtomicUsize::new(0),
    };

    /// Test setting an environment variable.
    #[test]
    fn test_with_var_set() {
        let env_key = &GENERATOR.next();

        crate::with_var(env_key, Some(env_key), || {
            assert_eq!(env::var(env_key), Ok(env_key.to_string()));
        });

        assert_eq!(env::var(env_key), Err(VarError::NotPresent));
    }

    /// Test unsetting an environment variable.
    #[test]
    fn test_with_var_set_to_none() {
        let env_key = &GENERATOR.next();
        unsafe { env::set_var(env_key, env_key) };

        crate::with_var(env_key, None::<&str>, || {
            assert_eq!(env::var(env_key), Err(VarError::NotPresent));
        });

        assert_eq!(env::var(env_key), Ok(env_key.to_string()));
    }

    /// Test setting an environment variable via shorthand.
    #[test]
    fn test_with_var_unset() {
        let env_key = &GENERATOR.next();
        unsafe { env::set_var(env_key, env_key) };

        crate::with_var_unset(env_key, || {
            assert_eq!(env::var(env_key), Err(VarError::NotPresent));
        });

        assert_eq!(env::var(env_key), Ok(env_key.to_string()));
    }

    /// Test overriding an environment variable.
    #[test]
    fn test_with_var_override() {
        let env_key = &GENERATOR.next();
        unsafe { env::set_var(env_key, env_key) };

        crate::with_var(env_key, Some("new"), || {
            assert_eq!(env::var(env_key), Ok("new".to_string()));
        });

        assert_eq!(env::var(env_key), Ok(env_key.to_string()));
    }

    /// Test with_var panic behavior.
    #[test]
    fn test_with_var_panic() {
        let env_key = &GENERATOR.next();
        unsafe { env::set_var(env_key, env_key) };

        let did_panic = panic::catch_unwind(|| {
            crate::with_var(env_key, Some("don't panic"), || {
                assert_eq!(env::var(env_key), Ok("don't panic".to_string()));
                panic!("abort this closure with a panic.");
            });
        });

        assert!(did_panic.is_err(), "The closure must panic.");
        assert_eq!(env::var(env_key), Ok(env_key.to_string()));
    }

    /// Test setting multiple environment variables.
    #[test]
    fn test_with_vars_set() {
        let env_key_1 = &GENERATOR.next();
        let env_key_2 = &GENERATOR.next();

        crate::with_vars(
            [(env_key_1, Some(env_key_1)), (env_key_2, Some(env_key_2))],
            || {
                assert_eq!(env::var(env_key_1), Ok(env_key_1.to_string()));
                assert_eq!(env::var(env_key_2), Ok(env_key_2.to_string()));
            },
        );

        assert_eq!(env::var(env_key_1), Err(VarError::NotPresent));
        assert_eq!(env::var(env_key_2), Err(VarError::NotPresent));
    }

    /// Test with_vars closure return behavior.
    #[test]
    fn test_with_vars_set_returning() {
        let env_key_1 = &GENERATOR.next();
        let env_key_2 = &GENERATOR.next();

        let r = crate::with_vars(
            [(env_key_1, Some(env_key_1)), (env_key_2, Some(env_key_2))],
            || {
                let one_is_set = env::var(env_key_1);
                let two_is_set = env::var(env_key_2);
                (one_is_set, two_is_set)
            },
        );

        let (one_from_closure, two_from_closure) = r;

        assert_eq!(one_from_closure, Ok(env_key_1.to_string()));
        assert_eq!(two_from_closure, Ok(env_key_2.to_string()));

        assert_eq!(env::var(env_key_1), Err(VarError::NotPresent));
        assert_eq!(env::var(env_key_2), Err(VarError::NotPresent));
    }

    /// Test unsetting multiple environment variables via shorthand.
    #[test]
    fn test_with_vars_unset() {
        let env_key_1 = &GENERATOR.next();
        let env_key_2 = &GENERATOR.next();
        unsafe { env::set_var(env_key_1, env_key_1) };

        crate::with_vars_unset([env_key_1, env_key_2], || {
            assert_eq!(env::var(env_key_1), Err(VarError::NotPresent));
            assert_eq!(env::var(env_key_2), Err(VarError::NotPresent));
        });

        assert_eq!(env::var(env_key_1), Ok(env_key_1.to_string()));
        assert_eq!(env::var(env_key_2), Err(VarError::NotPresent));
    }

    /// Test partially setting and unsetting environment variables.
    #[test]
    fn test_with_vars_partially_unset() {
        let env_key_1 = &GENERATOR.next();
        let env_key_2 = &GENERATOR.next();
        unsafe { env::set_var(env_key_2, env_key_2) };

        crate::with_vars(
            [(env_key_1, Some("set")), (env_key_2, None::<&str>)],
            || {
                assert_eq!(env::var(env_key_1), Ok("set".to_string()));
                assert_eq!(env::var(env_key_2), Err(VarError::NotPresent));
            },
        );

        assert_eq!(env::var(env_key_1), Err(VarError::NotPresent));
        assert_eq!(env::var(env_key_2), Ok(env_key_2.to_string()));
    }

    /// Test overriding multiple environment variables.
    #[test]
    fn test_with_vars_override() {
        let env_key_1 = &GENERATOR.next();
        let env_key_2 = &GENERATOR.next();
        unsafe { env::set_var(env_key_1, env_key_1) };
        unsafe { env::set_var(env_key_2, env_key_2) };

        crate::with_vars(
            [(env_key_1, Some("other")), (env_key_2, Some("value"))],
            || {
                assert_eq!(env::var(env_key_1), Ok("other".to_string()));
                assert_eq!(env::var(env_key_2), Ok("value".to_string()));
            },
        );

        assert_eq!(env::var(env_key_1), Ok(env_key_1.to_string()));
        assert_eq!(env::var(env_key_2), Ok(env_key_2.to_string()));
    }

    /// Test, when setting the same variable twice, the latter one is used.
    #[test]
    fn test_with_vars_same_vars() {
        let env_key = &GENERATOR.next();

        crate::with_vars(
            [(env_key, Some("initial")), (env_key, Some("override"))],
            || {
                assert_eq!(env::var(env_key), Ok("override".to_string()));
            },
        );

        assert_eq!(env::var(env_key), Err(VarError::NotPresent));
    }

    /// Test that unsetting and setting the same variable leads to the variable being set.
    #[test]
    fn test_with_vars_unset_set() {
        let env_key = &GENERATOR.next();
        unsafe { env::set_var(env_key, env_key) };

        crate::with_vars(
            [(env_key, None::<&str>), (env_key, Some("new value"))],
            || {
                assert_eq!(env::var(env_key), Ok("new value".to_string()));
            },
        );

        assert_eq!(env::var(env_key), Ok(env_key.to_string()));
    }

    /// Test that setting and unsetting the same variable leads to the variable being unset.
    #[test]
    fn test_with_vars_set_unset() {
        let env_key = &GENERATOR.next();

        crate::with_vars(
            [(env_key, Some("it is set")), (env_key, None::<&str>)],
            || {
                assert_eq!(env::var(env_key), Err(VarError::NotPresent));
            },
        );

        assert_eq!(env::var(env_key), Err(VarError::NotPresent));
    }

    #[test]
    fn test_with_nested_set() {
        let env_key_1 = &GENERATOR.next();
        let env_key_2 = &GENERATOR.next();

        crate::with_var(env_key_1, Some(env_key_1), || {
            crate::with_var(env_key_2, Some(env_key_2), || {
                assert_eq!(env::var(env_key_1), Ok(env_key_1.to_string()));
                assert_eq!(env::var(env_key_2), Ok(env_key_2.to_string()));
            })
        });

        assert_eq!(env::var(env_key_1), Err(VarError::NotPresent));
        assert_eq!(env::var(env_key_2), Err(VarError::NotPresent));
    }

    #[test]
    fn test_fn_once() {
        let env_key = &GENERATOR.next();
        let value = String::from("Hello, ");
        let value = crate::with_var(env_key, Some("world!"), || {
            value + &env::var(env_key).unwrap()
        });
        assert_eq!(value, "Hello, world!");
    }

    #[cfg(feature = "async_closure")]
    async fn check_var(env_key: &str) {
        let v = env::var(env_key).unwrap();
        assert_eq!(v, "ok".to_owned());
    }

    #[cfg(feature = "async_closure")]
    #[tokio::test]
    async fn test_async_closure() {
        let env_key = &GENERATOR.next();
        crate::async_with_vars([(env_key, Some("ok"))], check_var(env_key)).await;

        let f = async {
            let v = env::var(env_key).unwrap();
            assert_eq!(v, "ok".to_owned());
        };

        crate::async_with_vars([(env_key, Some("ok"))], f).await;
    }

    #[cfg(feature = "async_closure")]
    #[tokio::test(flavor = "multi_thread")]
    async fn test_async_closure_calls_closure() {
        let env_key = &GENERATOR.next();
        let (tx, rx) = tokio::sync::oneshot::channel();
        let f = async {
            tx.send(env::var(env_key)).unwrap();
        };
        crate::async_with_vars([(env_key, Some("ok"))], f).await;
        let value = rx.await.unwrap().unwrap();
        assert_eq!(value, "ok".to_owned());
    }

    #[cfg(feature = "async_closure")]
    #[tokio::test(flavor = "multi_thread")]
    async fn test_async_with_vars_set_returning() {
        let env_key_1 = &GENERATOR.next();
        let env_key_2 = &GENERATOR.next();

        let r = crate::async_with_vars(
            [(env_key_1, Some(env_key_1)), (env_key_2, Some(env_key_2))],
            async {
                let one_is_set = env::var(env_key_1).unwrap();
                let two_is_set = env::var(env_key_2).unwrap();
                (one_is_set, two_is_set)
            },
        )
        .await;

        let (one_from_closure, two_from_closure) = r;
        assert_eq!(one_from_closure, env_key_1.to_string());
        assert_eq!(two_from_closure, env_key_2.to_string());
        assert_eq!(env::var(env_key_1), Err(VarError::NotPresent));
        assert_eq!(env::var(env_key_2), Err(VarError::NotPresent));
    }
}
