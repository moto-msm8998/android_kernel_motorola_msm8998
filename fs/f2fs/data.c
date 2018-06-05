
	if (!is_valid_blkaddr(dn.data_blkaddr)) {
	/*
	 * If current allocation needs SSR,
	 * it had better in-place writes for updated data.
	 */
	if (unlikely(is_valid_blkaddr(fio->blk_addr) &&
			!is_cold_data(page) &&
			need_inplace_update(inode))) {
		rewrite_data_page(fio);
		set_inode_flag(F2FS_I(inode), FI_UPDATE_WRITE);
		trace_f2fs_do_write_data_page(page, IPU);
	} else {
		write_data_page(&dn, fio);
		set_data_blkaddr(&dn);
		f2fs_update_extent_cache(&dn);
		trace_f2fs_do_write_data_page(page, OPU);
		set_inode_flag(F2FS_I(inode), FI_APPEND_WRITE);
		if (page->index == 0)
			set_inode_flag(F2FS_I(inode), FI_FIRST_BLOCK_WRITTEN);
	}
{
	mempool_destroy(bio_post_read_ctx_pool);
	kmem_cache_destroy(bio_post_read_ctx_cache);
}
