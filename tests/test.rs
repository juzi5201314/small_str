use small_str::{SmallStr, SmallString};

#[test]
fn min_capacity() {
    let s = SmallStr::<10>::with_capacity(5);
    assert_eq!(s.capacity(), 10);
}

#[test]
fn inline() {
    // SmallString = SmallStr<16>
    let mut s = SmallString::from("1234567890123456");
    assert!(s.is_inlined());
    s.push_str("7");
    assert_eq!(s.len(), 17);
    assert!(!s.is_inlined());
}

#[cfg(feature = "serde")]
mod serde_tests {
    use small_str::SmallString;
    use serde::{Deserialize, Serialize};
    use std::collections::HashMap;

    #[derive(Serialize, Deserialize)]
    struct SmallStrStruct {
        pub(crate) s: SmallString,
        pub(crate) vec: Vec<SmallString>,
        pub(crate) map: HashMap<SmallString, SmallString>,
    }

    #[test]
    fn test_serde() {
        let s = SmallString::from("Hello, World");
        let s = serde_json::to_string(&s).unwrap();
        assert_eq!(s, "\"Hello, World\"");
        let s: SmallString = serde_json::from_str(&s).unwrap();
        assert_eq!(s, "Hello, World");
    }

    #[test]
    fn test_serde_reader() {
        let s = SmallString::from("Hello, World");
        let s = serde_json::to_string(&s).unwrap();
        assert_eq!(s, "\"Hello, World\"");
        let s: SmallString = serde_json::from_reader(std::io::Cursor::new(s)).unwrap();
        assert_eq!(s, "Hello, World");
    }

    #[test]
    fn test_serde_struct() {
        let mut map = HashMap::new();
        map.insert(SmallString::from("a"), SmallString::from("ohno"));
        let struct_ = SmallStrStruct {
            s: SmallString::from("Hello, World"),
            vec: vec![SmallString::from("Hello, World"), SmallString::from("Hello, World")],
            map,
        };
        let s = serde_json::to_string(&struct_).unwrap();
        let _new_struct: SmallStrStruct = serde_json::from_str(&s).unwrap();
    }

    #[test]
    fn test_serde_struct_reader() {
        let mut map = HashMap::new();
        map.insert(SmallString::from("a"), SmallString::from("ohno"));
        let struct_ = SmallStrStruct {
            s: SmallString::from("Hello, World"),
            vec: vec![SmallString::from("Hello, World"), SmallString::from("Hello, World")],
            map,
        };
        let s = serde_json::to_string(&struct_).unwrap();
        let _new_struct: SmallStrStruct = serde_json::from_reader(std::io::Cursor::new(s)).unwrap();
    }

    #[test]
    fn test_serde_hashmap() {
        let mut map = HashMap::new();
        map.insert(SmallString::from("a"), SmallString::from("ohno"));
        let s = serde_json::to_string(&map).unwrap();
        let _s: HashMap<SmallString, SmallString> = serde_json::from_str(&s).unwrap();
    }

    #[test]
    fn test_serde_hashmap_reader() {
        let mut map = HashMap::new();
        map.insert(SmallString::from("a"), SmallString::from("ohno"));
        let s = serde_json::to_string(&map).unwrap();
        let _s: HashMap<SmallString, SmallString> =
            serde_json::from_reader(std::io::Cursor::new(s)).unwrap();
    }

    #[test]
    fn test_serde_vec() {
        let vec = vec![SmallString::from(""), SmallString::from("b")];
        let s = serde_json::to_string(&vec).unwrap();
        let _s: Vec<SmallString> = serde_json::from_str(&s).unwrap();
    }

    #[test]
    fn test_serde_vec_reader() {
        let vec = vec![SmallString::from(""), SmallString::from("b")];
        let s = serde_json::to_string(&vec).unwrap();
        let _s: Vec<SmallString> = serde_json::from_reader(std::io::Cursor::new(s)).unwrap();
    }
}