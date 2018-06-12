/// A dummy allocator for tests.

mod dummy {
    extern crate core;
    use super::allocator_api::{Alloc, AllocErr, Layout};
    use self::core::ptr::NonNull;

    #[derive(Clone, Default)]
    pub struct MyHeap;

    static mut HEAP_BUF: [u8; 4096] = [0; 4096];
    static mut HEAP_CURSOR: usize = 0;

    unsafe impl<'a> Alloc for MyHeap {
        unsafe fn alloc(&mut self, layout: Layout) -> Result<NonNull<u8>, AllocErr> {
            let ptr = HEAP_BUF.as_ptr() as usize;
            let mut start = HEAP_CURSOR;
            let modulo = (ptr + start) & (layout.align() - 1);
            if modulo != 0 {
                start += layout.align() - modulo;
            }
            assert_eq!((ptr + start) & (layout.align() - 1), 0);
            let end = start + layout.size();
            let buf = HEAP_BUF.get_mut(start..end);
            HEAP_CURSOR = end;
            buf.map(|b| NonNull::new_unchecked(b as *mut [u8] as *mut u8))
                .ok_or_else(|| AllocErr)
        }
        unsafe fn dealloc(&mut self, _ptr: NonNull<u8>, _layout: Layout) {}
    }

}

use self::dummy::MyHeap;
